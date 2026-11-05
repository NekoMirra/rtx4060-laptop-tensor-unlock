/* SPDX-License-Identifier: GPL-2.0-only */
/* Display ownership adapter, board independent. The firmware's own GPU driver (whatever
 * agent holds the GPU's PciIo BY_DRIVER) is stopped with ONE DisconnectController, so the
 * UEFI core itself cascades through whatever console stack sits on top of its GOP children;
 * then this image takes the exclusive PciIo claim and restores only the IO/MEM decode the
 * driver cleared. After the transaction the claim is closed and the same driver is connected
 * again. Shape adapted from TOTORONG/AD103_win_unlocker (ownership.c, handoff.inc), which ran
 * this sequence on hardware. No driver code or data is patched. A card with no driver bound,
 * or no display children, is handled the same way (nothing to stop, nothing to reconnect). */
#include "release.h"
#include "boot_io.h"
#include "profile.h"
#include "sha256.h"
#include "compat/compat.h"
#include <Protocol/GraphicsOutput.h>
#include <Protocol/DriverBinding.h>
#include <Protocol/LoadedImage.h>
#include <Protocol/SimpleTextIn.h>
#include <Protocol/SimpleTextOut.h>
#include <IndustryStandard/Acpi10.h>

#define MAX_RECORDS 48
#define MAX_CHILDREN 8
typedef struct {EFI_GUID protocol;EFI_OPEN_PROTOCOL_INFORMATION_ENTRY entry;} RECORD;
typedef struct {
  EFI_HANDLE handle;VOID *gop;UINT64 framebuffer;UINTN framebuffer_size;
  UINT32 width,height,stride,format;BOOLEAN screen;UINT8 path_sha256[32];
} CHILD;
typedef struct {
  EFI_HANDLE agent,image;VOID *base;UINT64 size;UINT32 version;EFI_DRIVER_BINDING_STOP stop;
  UINTN child_count;CHILD children[MAX_CHILDREN];
} OWNER;
typedef struct {
  EFI_SYSTEM_TABLE *table;EFI_HANDLE self,pci,console_out,console_in,console_err;
  EFI_SIMPLE_TEXT_OUTPUT_PROTOCOL *text,*err;EFI_SIMPLE_TEXT_INPUT_PROTOCOL *keys;UINTN key_read;
  OWNER owner;UINT32 config[64];UINT64 attributes;UINT16 command_entry;
  BOOLEAN ready,mutated,claimed,bme_entry;
} PLAN;
static PLAN Plan;
static EFI_GUID PciGuid=EFI_PCI_IO_PROTOCOL_GUID,PathGuid=EFI_DEVICE_PATH_PROTOCOL_GUID,GopGuid=EFI_GRAPHICS_OUTPUT_PROTOCOL_GUID;
static EFI_GUID BindingGuid=EFI_DRIVER_BINDING_PROTOCOL_GUID,ImageGuid=EFI_LOADED_IMAGE_PROTOCOL_GUID;
/* v1 logging helper: GuLog faults the platform when no log is open, so guard it here. */
#define NOTE(...) do{if(GuBootLogOpen())GuLog(__VA_ARGS__);}while(0)

static BOOLEAN Passive(UINT32 a) {
  return a==EFI_OPEN_PROTOCOL_BY_HANDLE_PROTOCOL||a==EFI_OPEN_PROTOCOL_GET_PROTOCOL||a==EFI_OPEN_PROTOCOL_TEST_PROTOCOL;
}
/* Caller holds TPL_NOTIFY through the snapshot and, for the claim, the acquisition. */
static EFI_STATUS Snapshot(RECORD *records,UINTN *count) {
  EFI_GUID **protocols=NULL;UINTN pc=0;BOOLEAN pci=FALSE;*count=0;
  if(!Gu.bs->ProtocolsPerHandle||!Gu.bs->OpenProtocolInformation)return EFI_UNSUPPORTED;
  EFI_STATUS s=Gu.bs->ProtocolsPerHandle(Gu.handle,&protocols,&pc);
  if(!EFI_ERROR(s)&&(!protocols||!pc||pc>64))s=EFI_COMPROMISED_DATA;
  for(UINTN i=0;!EFI_ERROR(s)&&i<pc;i++) {
    EFI_OPEN_PROTOCOL_INFORMATION_ENTRY *entries=NULL;UINTN n=0;
    if(!protocols[i]){s=EFI_COMPROMISED_DATA;break;}
    if(!memcmp(protocols[i],&PciGuid,sizeof(PciGuid)))pci=TRUE;
    s=Gu.bs->OpenProtocolInformation(Gu.handle,protocols[i],&entries,&n);
    if(!EFI_ERROR(s)&&(n>MAX_RECORDS-*count||(n&&!entries)))s=EFI_COMPROMISED_DATA;
    if(!EFI_ERROR(s))for(UINTN j=0;j<n;j++){records[*count].protocol=*protocols[i];records[*count].entry=entries[j];(*count)++;}
    if(entries&&EFI_ERROR(Gu.bs->FreePool(entries)))s=EFI_DEVICE_ERROR;
  }
  if(protocols&&EFI_ERROR(Gu.bs->FreePool(protocols)))s=EFI_DEVICE_ERROR;
  return !EFI_ERROR(s)&&!pci?EFI_NOT_FOUND:s;
}
static VOID LogRecords(const RECORD *r,UINTN count,EFI_STATUS s) {
  NOTE("ownership: records=%zu exclusive=%u status=%#llx\n",(size_t)count,Gu.owned,(unsigned long long)s);
  for(UINTN i=0;i<count;i++)
    NOTE("owner[%u] protocol=%08x attributes=%#x count=%u agent=%#llx controller=%#llx\n",(unsigned)i,
      r[i].protocol.Data1,r[i].entry.Attributes,r[i].entry.OpenCount,
      (unsigned long long)(UINTN)r[i].entry.AgentHandle,(unsigned long long)(UINTN)r[i].entry.ControllerHandle);
}
static BOOLEAN IsGuid(const EFI_GUID *a,const EFI_GUID *b){return !memcmp(a,b,sizeof(EFI_GUID));}
/* A screen: a GOP with a sane linear framebuffer mode. */
static BOOLEAN Screen(const EFI_GRAPHICS_OUTPUT_PROTOCOL *gop) {
  const EFI_GRAPHICS_OUTPUT_PROTOCOL_MODE *m=gop?gop->Mode:NULL;
  return m&&m->Info&&m->SizeOfInfo>=sizeof(*m->Info)&&m->FrameBufferBase&&m->FrameBufferSize&&
    m->Info->HorizontalResolution&&m->Info->VerticalResolution&&
    m->Info->PixelFormat<=PixelBlueGreenRedReserved8BitPerColor&&
    m->Info->PixelsPerScanLine>=m->Info->HorizontalResolution&&
    (UINT64)m->Info->PixelsPerScanLine*m->Info->VerticalResolution<=m->FrameBufferSize/4;
}
/* The handle's device path: well formed and descending from this GPU. EFI_NOT_FOUND: no path. */
static EFI_STATUS GpuPath(EFI_HANDLE handle,EFI_DEVICE_PATH_PROTOCOL **out,UINTN *out_bytes) {
  EFI_DEVICE_PATH_PROTOCOL *path=NULL;
  EFI_STATUS s=Gu.bs->HandleProtocol(handle,&PathGuid,(VOID **)&path);
  if(EFI_ERROR(s)||!path)return EFI_NOT_FOUND;
  if(!Gu.bs->LocateDevicePath)return EFI_UNSUPPORTED;
  UINTN bytes=0;BOOLEAN end=FALSE;
  for(UINTN i=0;i<128&&bytes<=4092;i++) {
    EFI_DEVICE_PATH_PROTOCOL *node=(VOID *)((UINT8 *)path+bytes);
    UINTN length=node->Length[0]+((UINTN)node->Length[1]<<8);
    if(length<4||length>4096-bytes)return EFI_COMPROMISED_DATA;
    bytes+=length;
    if(node->Type==END_DEVICE_PATH_TYPE){if(node->SubType!=END_ENTIRE_DEVICE_PATH_SUBTYPE||length!=4)return EFI_UNSUPPORTED;end=TRUE;break;}
  }
  if(!end)return EFI_COMPROMISED_DATA;
  EFI_DEVICE_PATH_PROTOCOL *remaining=path;EFI_HANDLE parent=NULL;
  s=Gu.bs->LocateDevicePath(&PciGuid,&remaining,&parent);
  if(EFI_ERROR(s)||parent!=Gu.handle)return EFI_ACCESS_DENIED;
  *out=path;*out_bytes=bytes;return EFI_SUCCESS;
}
/* One display child of the GPU's driver, recorded whole so the check before the release covers it. The
   firmware lights one monitor and keeps a child for each further connected output, which may have no GOP,
   no mode or a blt-only one: such an output is a child without a screen. A child with a GOP must have a
   device path that descends from this GPU; one without a GOP may have no path at all. */
static EFI_STATUS DescribeChild(EFI_HANDLE handle,CHILD *c) {
  EFI_GRAPHICS_OUTPUT_PROTOCOL *gop=NULL;EFI_DEVICE_PATH_PROTOCOL *path=NULL;UINTN bytes=0;
  if(EFI_ERROR(Gu.bs->HandleProtocol(handle,&GopGuid,(VOID **)&gop)))gop=NULL;
  EFI_STATUS s=GpuPath(handle,&path,&bytes);
  if(s==EFI_NOT_FOUND&&!gop)path=NULL;
  else if(EFI_ERROR(s))return s;
  c->handle=handle;c->gop=gop;c->screen=Screen(gop);
  if(path)GuSha256(path,bytes,c->path_sha256);
  const EFI_GRAPHICS_OUTPUT_PROTOCOL_MODE *m=gop?gop->Mode:NULL;
  if(m){
    c->framebuffer=m->FrameBufferBase;c->framebuffer_size=m->FrameBufferSize;
    if(m->Info&&m->SizeOfInfo>=sizeof(*m->Info)){
      c->width=m->Info->HorizontalResolution;c->height=m->Info->VerticalResolution;
      c->stride=m->Info->PixelsPerScanLine;c->format=m->Info->PixelFormat;
    }
  }
  return EFI_SUCCESS;
}
static EFI_STATUS DisplayChild(const RECORD *r,OWNER *o) {
  const EFI_OPEN_PROTOCOL_INFORMATION_ENTRY *e=&r->entry;
  if(e->Attributes!=EFI_OPEN_PROTOCOL_BY_CHILD_CONTROLLER||e->AgentHandle!=o->agent||e->OpenCount!=1||
     !e->ControllerHandle||e->ControllerHandle==Gu.handle||e->ControllerHandle==Gu.image||
     o->child_count>=MAX_CHILDREN||(!IsGuid(&r->protocol,&PciGuid)&&!IsGuid(&r->protocol,&PathGuid)))return EFI_ACCESS_DENIED;
  for(UINTN i=0;i<o->child_count;i++)if(o->children[i].handle==e->ControllerHandle)return EFI_COMPROMISED_DATA;
  EFI_STATUS s=DescribeChild(e->ControllerHandle,&o->children[o->child_count]);
  if(!EFI_ERROR(s))o->child_count++;
  return s;
}
/* Who holds the GPU. At most one driver, owning the PciIo BY_DRIVER, with display children only.
 * No driver at all is valid, provided nobody else holds anything non-passive. */
static EFI_STATUS FindOwner(OWNER *o,BOOLEAN log) {
  RECORD records[MAX_RECORDS];UINTN count=0,drivers=0;memset(o,0,sizeof(*o));
  if(!Gu.bs->DisconnectController||Gu.owned)return EFI_UNSUPPORTED;
  EFI_TPL old=Gu.bs->RaiseTPL(TPL_NOTIFY);
  EFI_STATUS s=Snapshot(records,&count);
  Gu.bs->RestoreTPL(old);if(log)LogRecords(records,count,s);
  if(EFI_ERROR(s))return s;
  for(UINTN i=0;i<count;i++) {
    const EFI_OPEN_PROTOCOL_INFORMATION_ENTRY *e=&records[i].entry;
    if(IsGuid(&records[i].protocol,&PciGuid)&&(e->Attributes&(EFI_OPEN_PROTOCOL_BY_DRIVER|EFI_OPEN_PROTOCOL_EXCLUSIVE))) {
      if(e->Attributes!=EFI_OPEN_PROTOCOL_BY_DRIVER||!e->AgentHandle||e->ControllerHandle!=Gu.handle||e->OpenCount!=1)return EFI_ACCESS_DENIED;
      o->agent=e->AgentHandle;drivers++;
    }
  }
  if(drivers>1||(drivers&&(o->agent==Gu.image||o->agent==Gu.handle||o->agent==Plan.console_out||o->agent==Plan.console_in||o->agent==Plan.console_err)))
    return EFI_ACCESS_DENIED;
  for(UINTN i=0;i<count;i++) {
    const EFI_OPEN_PROTOCOL_INFORMATION_ENTRY *e=&records[i].entry;
    if(Passive(e->Attributes))continue;
    if(!drivers){if(log)NOTE("release refused: non-passive open with no driver bound at record %u\n",(unsigned)i);return EFI_ACCESS_DENIED;}
    if(e->Attributes==EFI_OPEN_PROTOCOL_BY_CHILD_CONTROLLER) {
      s=DisplayChild(&records[i],o);
      if(log)NOTE("display child: record=%u handle=%#llx status=%#llx\n",(unsigned)i,(unsigned long long)(UINTN)e->ControllerHandle,(unsigned long long)s);
      if(EFI_ERROR(s))return s;
      continue;
    }
    if(e->Attributes!=EFI_OPEN_PROTOCOL_BY_DRIVER||e->AgentHandle!=o->agent||e->ControllerHandle!=Gu.handle||e->OpenCount!=1) {
      if(log)NOTE("release refused: different owner or unsupported open at record %u\n",(unsigned)i);
      return EFI_ACCESS_DENIED;
    }
  }
  if(!drivers)return EFI_SUCCESS;
  EFI_DRIVER_BINDING_PROTOCOL *binding=NULL;EFI_LOADED_IMAGE_PROTOCOL *image=NULL;
  s=Gu.bs->HandleProtocol(o->agent,&BindingGuid,(VOID **)&binding);
  if(EFI_ERROR(s)||!binding||binding->DriverBindingHandle!=o->agent||!binding->Stop||!binding->ImageHandle||binding->ImageHandle==Gu.image)return EFI_UNSUPPORTED;
  s=Gu.bs->HandleProtocol(binding->ImageHandle,&ImageGuid,(VOID **)&image);
  if(EFI_ERROR(s)||!image)return EFI_UNSUPPORTED;
  if(log){
    static const char digits[]="0123456789abcdef";UINT8 d[32];char hex[65];
    if(image->ImageBase&&image->ImageSize&&image->ImageSize<=64U*1024U*1024U)GuSha256(image->ImageBase,image->ImageSize,d);else memset(d,0,32);
    for(UINTN i=0;i<32;i++){hex[2*i]=digits[d[i]>>4];hex[2*i+1]=digits[d[i]&15];}hex[64]=0;
    NOTE("release candidate: agent=%#llx image=%#llx source=%#llx base=%#llx bytes=%llu version=%#x code_type=%u children=%zu sha256=%s\n",
      (unsigned long long)(UINTN)o->agent,(unsigned long long)(UINTN)binding->ImageHandle,(unsigned long long)(UINTN)image->DeviceHandle,
      (unsigned long long)(UINTN)image->ImageBase,(unsigned long long)image->ImageSize,binding->Version,(unsigned)image->ImageCodeType,
      (size_t)o->child_count,hex);
  }
  if(!image->ImageBase||!image->ImageSize||image->ImageSize>64U*1024U*1024U||image->ImageCodeType!=EfiBootServicesCode)return EFI_UNSUPPORTED;
  o->image=binding->ImageHandle;o->base=image->ImageBase;o->size=image->ImageSize;o->version=binding->Version;o->stop=binding->Stop;
  return EFI_SUCCESS;
}
static BOOLEAN SameOwner(const OWNER *a,const OWNER *b) {
  if(a->agent!=b->agent||a->image!=b->image||a->base!=b->base||a->size!=b->size||a->version!=b->version||
     a->stop!=b->stop||a->child_count!=b->child_count)return FALSE;
  for(UINTN i=0;i<a->child_count;i++) {
    BOOLEAN match=FALSE;
    for(UINTN j=0;j<b->child_count;j++)if(!memcmp(&a->children[i],&b->children[j],sizeof(CHILD)))match=TRUE;
    if(!match)return FALSE;
  }
  return TRUE;
}
/* GOPs with a framebuffer whose device path descends from this GPU: screens, and the rest (a mode
   that is not a screen). GOPs of other devices, and virtual or blt-only ones, are not counted. */
static EFI_STATUS SurveyPathShape(const EFI_DEVICE_PATH_PROTOCOL *path,UINTN *bytes);
typedef struct {
  EFI_HANDLE handle,parent;EFI_GRAPHICS_OUTPUT_PROTOCOL *gop;
  EFI_GRAPHICS_OUTPUT_PROTOCOL_MODE *mode_ptr,mode;
  EFI_GRAPHICS_OUTPUT_MODE_INFORMATION info;
  EFI_DEVICE_PATH_PROTOCOL *path;EFI_PCI_IO_PROTOCOL *parent_pci;
  EFI_STATUS path_status;UINTN path_bytes;UINT8 path_sha256[32];
} GOP_VIEW;
/* Bounded scratch, like Plan: no allocation/free callback after the final memory comparison.
   Refuse reentry rather than allowing a firmware callback to overwrite an active snapshot. */
static GOP_VIEW AliasViews[128];static BOOLEAN AliasBusy,AliasProofUsed;static UINTN AliasViewCount;
static BOOLEAN MissingPath(EFI_STATUS s,const VOID *p){return !p&&(s==EFI_UNSUPPORTED||s==EFI_NOT_FOUND);}
static BOOLEAN HasFramebuffer(const GOP_VIEW *v){return v->mode_ptr&&(v->mode.FrameBufferBase||v->mode.FrameBufferSize);}
static BOOLEAN RangeValid(UINT64 base,UINT64 size){return base&&size&&size<=~(UINT64)0-base;}
static BOOLEAN Overlap(UINT64 a,UINT64 an,UINT64 b,UINT64 bn){return a<b+bn&&b<a+an;}
/* The existing Screen predicate, applied to a captured view for count consistency. */
static BOOLEAN CountedViewScreen(const GOP_VIEW *v){
  const EFI_GRAPHICS_OUTPUT_PROTOCOL_MODE *m=&v->mode;
  return v->mode_ptr&&m->Info&&m->SizeOfInfo>=sizeof(v->info)&&m->FrameBufferBase&&m->FrameBufferSize&&
    v->info.HorizontalResolution&&v->info.VerticalResolution&&
    v->info.PixelFormat<=PixelBlueGreenRedReserved8BitPerColor&&v->info.PixelsPerScanLine>=v->info.HorizontalResolution&&
    (UINT64)v->info.PixelsPerScanLine*v->info.VerticalResolution<=m->FrameBufferSize/4;
}
static BOOLEAN ViewScreen(const GOP_VIEW *v){
  return CountedViewScreen(v)&&v->mode.SizeOfInfo==sizeof(v->info)&&
    RangeValid(v->mode.FrameBufferBase,v->mode.FrameBufferSize)&&v->mode.MaxMode&&v->mode.Mode<v->mode.MaxMode;
}
static BOOLEAN ReadGopView(EFI_HANDLE h,GOP_VIEW *v){
  memset(v,0,sizeof(*v));v->handle=h;
  EFI_STATUS s=Gu.bs->HandleProtocol(h,&GopGuid,(VOID **)&v->gop);
  if(EFI_ERROR(s)||!v->gop)return FALSE;
  v->mode_ptr=v->gop->Mode;
  if(v->mode_ptr){
    memcpy(&v->mode,v->mode_ptr,sizeof(v->mode));
    /* Only the complete, known Info layout can be compared. Unknown extension bytes refuse. */
    if(v->mode.Info){if(v->mode.SizeOfInfo!=sizeof(v->info))return FALSE;memcpy(&v->info,v->mode.Info,sizeof(v->info));}
    else if(v->mode.SizeOfInfo||HasFramebuffer(v))return FALSE;
    if(HasFramebuffer(v)&&!RangeValid(v->mode.FrameBufferBase,v->mode.FrameBufferSize))return FALSE;
  }
  v->path_status=Gu.bs->HandleProtocol(h,&PathGuid,(VOID **)&v->path);
  if(MissingPath(v->path_status,v->path))return TRUE;
  if(v->path_status!=EFI_SUCCESS||!v->path||SurveyPathShape(v->path,&v->path_bytes)!=EFI_SUCCESS)return FALSE;
  GuSha256(v->path,v->path_bytes,v->path_sha256);
  if(HasFramebuffer(v)){
    EFI_DEVICE_PATH_PROTOCOL *left=v->path;
    s=Gu.bs->LocateDevicePath(&PciGuid,&left,&v->parent);
    if(EFI_ERROR(s)||!v->parent)return FALSE;
    s=Gu.bs->HandleProtocol(v->parent,&PciGuid,(VOID **)&v->parent_pci);
    if(EFI_ERROR(s)||!v->parent_pci)return FALSE;
  }
  return TRUE;
}
/* No callbacks: catch changes to an earlier snapshot during any later protocol/path callback. */
static BOOLEAN GopViewMemoryStable(const GOP_VIEW *v){
  if(v->gop->Mode!=v->mode_ptr)return FALSE;
  if(v->mode_ptr&&(memcmp(v->mode_ptr,&v->mode,sizeof(v->mode))||
      (v->mode.Info&&memcmp(v->mode.Info,&v->info,sizeof(v->info)))))return FALSE;
  if(v->path){UINTN bytes=0;UINT8 hash[32];
    if(SurveyPathShape(v->path,&bytes)!=EFI_SUCCESS||bytes!=v->path_bytes)return FALSE;
    GuSha256(v->path,bytes,hash);if(memcmp(hash,v->path_sha256,sizeof hash))return FALSE;
  }
  return TRUE;
}
static BOOLEAN SameFramebufferMode(const GOP_VIEW *a,const GOP_VIEW *b){
  return ViewScreen(a)&&ViewScreen(b)&&a->mode.MaxMode==b->mode.MaxMode&&a->mode.Mode==b->mode.Mode&&
    a->mode.SizeOfInfo==b->mode.SizeOfInfo&&a->mode.FrameBufferBase==b->mode.FrameBufferBase&&
    a->mode.FrameBufferSize==b->mode.FrameBufferSize&&!memcmp(&a->info,&b->info,sizeof(a->info));
}
static BOOLEAN ProveConsoleAliases(EFI_HANDLE *handles,UINTN count,UINTN screens,UINTN rest){
  if(!count||count>128)return FALSE;
  for(UINTN i=0;i<count;i++){
    for(UINTN j=0;j<i;j++)if(handles[i]==handles[j])return FALSE;
    if(!ReadGopView(handles[i],&AliasViews[i]))return FALSE;
  }
  /* The fresh enumeration must describe the same set; its allocation is freed before
     re-reading protocols and before the final callback-free memory comparison. */
  EFI_HANDLE *fresh=NULL;UINTN n=0;
  EFI_STATUS s=Gu.bs->LocateHandleBuffer(ByProtocol,&GopGuid,NULL,&n,&fresh);
  BOOLEAN same=s==EFI_SUCCESS&&fresh&&n==count;
  if(same)for(UINTN i=0;i<count;i++){
    UINTN matches=0;for(UINTN j=0;j<n;j++)if(handles[i]==fresh[j])matches++;
    if(matches!=1)same=FALSE;
  }
  if(fresh&&Gu.bs->FreePool(fresh)!=EFI_SUCCESS)same=FALSE;
  if(!same)return FALSE;
  for(UINTN i=0;i<count;i++){
    GOP_VIEW again;if(!ReadGopView(handles[i],&again)||memcmp(&again,&AliasViews[i],sizeof again))return FALSE;
  }
  for(UINTN i=0;i<count;i++)if(!GopViewMemoryStable(&AliasViews[i]))return FALSE;
  /* Proof callbacks may have changed a physical GOP after the original traversal.
     The same stable views proving aliases must also agree with its target count. */
  UINTN fresh_screens=0,fresh_rest=0;
  for(UINTN i=0;i<count;i++)if(AliasViews[i].parent==Gu.handle&&HasFramebuffer(&AliasViews[i])){
    if(CountedViewScreen(&AliasViews[i]))fresh_screens++;else fresh_rest++;
  }
  if(fresh_screens!=screens||fresh_rest!=rest)return FALSE;
  for(UINTN i=0;i<count;i++){
    const GOP_VIEW *a=&AliasViews[i];
    if(a->path||!HasFramebuffer(a))continue;
    if(!MissingPath(a->path_status,a->path)||(a->handle!=Plan.console_out&&a->handle!=Plan.console_err)||!ViewScreen(a))return FALSE;
    UINT64 base=a->mode.FrameBufferBase,size=a->mode.FrameBufferSize;
    /* Retain the target's preflight ranges even while its physical GOP is temporarily gone. */
    for(UINTN j=0;j<Plan.owner.child_count;j++){
      const CHILD *c=&Plan.owner.children[j];
      if(!(c->framebuffer||c->framebuffer_size))continue;
      if(!RangeValid(c->framebuffer,c->framebuffer_size)||Overlap(base,size,c->framebuffer,c->framebuffer_size))return FALSE;
    }
    UINTN matches=0;
    for(UINTN j=0;j<count;j++){
      const GOP_VIEW *p=&AliasViews[j];if(!p->path||!HasFramebuffer(p))continue;
      if(p->parent==Gu.handle){if(Overlap(base,size,p->mode.FrameBufferBase,p->mode.FrameBufferSize))return FALSE;}
      else if(p->parent&&p->parent_pci&&SameFramebufferMode(a,p))matches++;
    }
    if(matches!=1)return FALSE;
  }
  return TRUE;
}
/* log is TRUE only in preflight, never in release's quiet window or at raised TPL. */
static EFI_STATUS GopCount(UINTN *screens,UINTN *rest,BOOLEAN log) {
  EFI_HANDLE *h=NULL;UINTN count=0;*screens=*rest=0;
  BOOLEAN deferred_alias=FALSE;
  EFI_STATUS s=Gu.bs->LocateHandleBuffer(ByProtocol,&GopGuid,NULL,&count,&h);
  if(log)NOTE("preflight GOP enumeration: status=%#llx count=%zu buffer=%#llx\n",(unsigned long long)s,(size_t)count,(unsigned long long)(UINTN)h);
  if(s==EFI_NOT_FOUND)return EFI_SUCCESS;
  if(s==EFI_SUCCESS&&(!h||!count||count>128))s=EFI_UNSUPPORTED;
  for(UINTN i=0;s==EFI_SUCCESS&&i<count;i++) {
    EFI_GRAPHICS_OUTPUT_PROTOCOL *g=NULL;EFI_DEVICE_PATH_PROTOCOL *path=NULL;UINTN bytes=0;
    s=Gu.bs->HandleProtocol(h[i],&GopGuid,(VOID **)&g);
    if(log)NOTE("preflight GOP[%u]: handle=%#llx protocol_status=%#llx protocol=%#llx console_out_handle=%u console_in_handle=%u console_err_handle=%u\n",(unsigned)i,
      (unsigned long long)(UINTN)h[i],(unsigned long long)s,(unsigned long long)(UINTN)g,
      h[i]==Plan.console_out,h[i]==Plan.console_in,h[i]==Plan.console_err);
    if(EFI_ERROR(s)||!g){if(log)NOTE("preflight GOP[%u]: reason=invalid-gop-protocol\n",(unsigned)i);s=EFI_COMPROMISED_DATA;break;}
    const EFI_GRAPHICS_OUTPUT_PROTOCOL_MODE *m=g->Mode;
    const EFI_GRAPHICS_OUTPUT_MODE_INFORMATION *info=m&&m->Info&&m->SizeOfInfo>=sizeof(*m->Info)?m->Info:NULL;
    if(log)NOTE("preflight GOP[%u]: mode=%#llx info=%#llx info_bytes=%zu max_mode=%u mode_index=%u fb=%#llx fb_bytes=%#llx width=%u height=%u stride=%u format=%u screen=%u\n",
      (unsigned)i,(unsigned long long)(UINTN)m,(unsigned long long)(UINTN)(m?m->Info:NULL),m?(size_t)m->SizeOfInfo:0,
      m?m->MaxMode:0,m?m->Mode:0,(unsigned long long)(m?m->FrameBufferBase:0),(unsigned long long)(m?m->FrameBufferSize:0),
      info?info->HorizontalResolution:0,info?info->VerticalResolution:0,info?info->PixelsPerScanLine:0,info?(unsigned)info->PixelFormat:0,Screen(g));
    if(!g->Mode||(!g->Mode->FrameBufferBase&&!g->Mode->FrameBufferSize)){
      if(log)NOTE("preflight GOP[%u]: path_lookup=not-required reason=no-framebuffer-or-mode\n",(unsigned)i);
      continue; /* virtual / blt-only: unchanged admission rule */
    }
    EFI_STATUS path_status=Gu.bs->HandleProtocol(h[i],&PathGuid,(VOID **)&path);
    if(log)NOTE("preflight GOP[%u]: path_status=%#llx path=%#llx\n",(unsigned)i,(unsigned long long)path_status,(unsigned long long)(UINTN)path);
    if(path_status!=EFI_SUCCESS||!path){
      if(MissingPath(path_status,path)&&(h[i]==Plan.console_out||h[i]==Plan.console_err)){
        deferred_alias=TRUE;if(log)NOTE("preflight GOP[%u]: reason=console-alias-requires-proof\n",(unsigned)i);continue;
      }
      if(log)NOTE("preflight GOP[%u]: reason=missing-device-path\n",(unsigned)i);s=EFI_UNSUPPORTED;break;
    }
    /* Validate the entire bounded path before a firmware resolver may walk it. */
    s=SurveyPathShape(path,&bytes);if(EFI_ERROR(s))break;
    EFI_HANDLE parent=NULL;EFI_DEVICE_PATH_PROTOCOL *left=path;
    EFI_STATUS parent_status=Gu.bs->LocateDevicePath(&PciGuid,&left,&parent);
    if(log)NOTE("preflight GOP[%u]: parent_status=%#llx parent=%#llx target_handle=%#llx target=%u remaining=%#llx\n",(unsigned)i,
      (unsigned long long)parent_status,(unsigned long long)(UINTN)parent,(unsigned long long)(UINTN)Gu.handle,
      !EFI_ERROR(parent_status)&&parent==Gu.handle,(unsigned long long)(UINTN)left);
    if(EFI_ERROR(parent_status)||parent!=Gu.handle)continue; /* another device's */
    s=GpuPath(h[i],&path,&bytes);
    if(log)NOTE("preflight GOP[%u]: target_path_status=%#llx path_bytes=%zu\n",(unsigned)i,(unsigned long long)s,(size_t)bytes);
    if(EFI_ERROR(s))break; /* ours, malformed path */
    if(Screen(g))(*screens)++;else (*rest)++;
  }
  if(s==EFI_SUCCESS&&deferred_alias){
    BOOLEAN valid=ProveConsoleAliases(h,count,*screens,*rest);AliasProofUsed=valid;AliasViewCount=valid?count:0;
    if(log)NOTE("preflight console GOP alias: verified=%u policy=unique-stable-non-target-framebuffer\n",valid);
    if(!valid)s=EFI_UNSUPPORTED;
  }
  if(h)Gu.bs->FreePool(h);
  return s;
}
/* attached: the driver's screens are back (at least one if it had any); released: no GOP of this GPU remains. */
static BOOLEAN GopsChecked(BOOLEAN attached,BOOLEAN log) {
  if(AliasBusy)return FALSE;AliasBusy=TRUE;AliasProofUsed=FALSE;AliasViewCount=0;
  UINTN screens,rest,want=0;EFI_STATUS s=GopCount(&screens,&rest,log);
  for(UINTN i=0;i<Plan.owner.child_count;i++)if(Plan.owner.children[i].screen)want++;
  BOOLEAN ok;
  if(EFI_ERROR(s))ok=FALSE;
  else if(!attached)ok=!screens&&!rest;
  else if(want)ok=screens>0&&screens<=MAX_CHILDREN;
  else ok=Plan.owner.child_count?screens<=MAX_CHILDREN:!screens;
  if(log)NOTE("preflight GOP check: enum_status=%#llx attached=%u owner_children=%zu required_screens=%zu screens=%zu rest=%zu accepted=%u reason=%s\n",
    (unsigned long long)s,attached,(size_t)Plan.owner.child_count,(size_t)want,(size_t)screens,(size_t)rest,ok,
    EFI_ERROR(s)?"enumeration-refused":ok?"accepted":!attached?"target-gop-still-present":
    want&&!screens?"required-target-screen-missing":screens>MAX_CHILDREN?"too-many-target-screens":"unexpected-target-screen");
  /* GopCount's FreePool and the optional preflight log are callbacks too. Recheck
     after both, with the scratch protected against reentry, before returning success. */
  if(ok&&AliasProofUsed)for(UINTN i=0;i<AliasViewCount;i++)
    if(!GopViewMemoryStable(&AliasViews[i])){ok=FALSE;break;}
  AliasBusy=FALSE;return ok;
}
static BOOLEAN Gops(BOOLEAN attached){return GopsChecked(attached,FALSE);}
/* A refusal must stay a refusal. This second, independent survey runs only after that
   decision, so a pathless first GOP cannot hide later physical GOPs or framebuffer aliases.
   It never participates in admission, runs at normal preflight TPL, and continues after
   errors on individual handles. Device paths are bounded before LocateDevicePath. */
static EFI_STATUS SurveyPathShape(const EFI_DEVICE_PATH_PROTOCOL *path,UINTN *bytes) {
  *bytes=0;
  for(UINTN i=0;i<128&&*bytes<=4092;i++) {
    const EFI_DEVICE_PATH_PROTOCOL *node=(const VOID *)((const UINT8 *)path+*bytes);
    UINTN length=node->Length[0]+((UINTN)node->Length[1]<<8);
    if(length<4||length>4096-*bytes)return EFI_COMPROMISED_DATA;
    *bytes+=length;
    if(node->Type==END_DEVICE_PATH_TYPE)
      return node->SubType==END_ENTIRE_DEVICE_PATH_SUBTYPE&&length==4?EFI_SUCCESS:EFI_UNSUPPORTED;
  }
  return EFI_COMPROMISED_DATA;
}
static VOID SurveyGopsAfterRefusal(VOID) {
  EFI_HANDLE *handles=NULL;UINTN count=0;
  EFI_STATUS s=Gu.bs->LocateHandleBuffer(ByProtocol,&GopGuid,NULL,&count,&handles);
  NOTE("preflight GOP survey: admission_already_refused=1 enum_status=%#llx count=%zu buffer=%#llx\n",
    (unsigned long long)s,(size_t)count,(unsigned long long)(UINTN)handles);
  if(s!=EFI_SUCCESS||!handles||!count||count>128) {
    NOTE("preflight GOP survey incomplete: enum_status=%#llx count=%zu max_handles=128\n",(unsigned long long)s,(size_t)count);
    if(handles)Gu.bs->FreePool(handles);
    return;
  }
  for(UINTN i=0;i<count;i++) {
    EFI_GRAPHICS_OUTPUT_PROTOCOL *g=NULL;EFI_DEVICE_PATH_PROTOCOL *path=NULL;EFI_HANDLE parent=NULL;
    EFI_STATUS gs=Gu.bs->HandleProtocol(handles[i],&GopGuid,(VOID **)&g);
    const EFI_GRAPHICS_OUTPUT_PROTOCOL_MODE *m=!EFI_ERROR(gs)&&g?g->Mode:NULL;
    const EFI_GRAPHICS_OUTPUT_MODE_INFORMATION *info=m&&m->Info&&m->SizeOfInfo>=sizeof(*m->Info)?m->Info:NULL;
    NOTE("preflight GOP survey[%u]: handle=%#llx protocol_status=%#llx protocol=%#llx console_out_handle=%u console_in_handle=%u console_err_handle=%u\n",
      (unsigned)i,(unsigned long long)(UINTN)handles[i],(unsigned long long)gs,(unsigned long long)(UINTN)g,
      handles[i]==Plan.console_out,handles[i]==Plan.console_in,handles[i]==Plan.console_err);
    NOTE("preflight GOP survey[%u]: mode=%#llx info=%#llx info_bytes=%zu max_mode=%u mode_index=%u fb=%#llx fb_bytes=%#llx width=%u height=%u stride=%u format=%u screen=%u\n",
      (unsigned)i,(unsigned long long)(UINTN)m,(unsigned long long)(UINTN)(m?m->Info:NULL),m?(size_t)m->SizeOfInfo:0,
      m?m->MaxMode:0,m?m->Mode:0,(unsigned long long)(m?m->FrameBufferBase:0),(unsigned long long)(m?m->FrameBufferSize:0),
      info?info->HorizontalResolution:0,info?info->VerticalResolution:0,info?info->PixelsPerScanLine:0,info?(unsigned)info->PixelFormat:0,
      !EFI_ERROR(gs)&&g?Screen(g):FALSE);
    EFI_STATUS ps=Gu.bs->HandleProtocol(handles[i],&PathGuid,(VOID **)&path);
    UINTN bytes=0;EFI_STATUS shape=ps==EFI_SUCCESS&&path?SurveyPathShape(path,&bytes):EFI_NOT_FOUND;
    EFI_STATUS parent_status=EFI_NOT_READY;BOOLEAN looked=FALSE;
    if(shape==EFI_SUCCESS){EFI_DEVICE_PATH_PROTOCOL *left=path;looked=TRUE;parent_status=Gu.bs->LocateDevicePath(&PciGuid,&left,&parent);}
    NOTE("preflight GOP survey[%u]: path_status=%#llx path=%#llx path_shape_status=%#llx path_bytes=%zu parent_lookup=%u parent_status=%#llx parent=%#llx target_handle=%#llx target_known=%u target=%u\n",
      (unsigned)i,(unsigned long long)ps,(unsigned long long)(UINTN)path,(unsigned long long)shape,(size_t)bytes,looked,
      (unsigned long long)parent_status,(unsigned long long)(UINTN)parent,(unsigned long long)(UINTN)Gu.handle,
      looked&&!EFI_ERROR(parent_status),looked&&!EFI_ERROR(parent_status)&&parent==Gu.handle);
  }
  Gu.bs->FreePool(handles);
  NOTE("preflight GOP survey complete: examined=%zu admission_still_refused=1\n",(size_t)count);
}
static EFI_STATUS AliveChecked(BOOLEAN log) {
  EFI_SYSTEM_TABLE *t=Plan.table;
  /* Decide with the original short-circuit expression before any diagnostic callback. */
  BOOLEAN changed=t->ConsoleOutHandle!=Plan.console_out||t->ConsoleInHandle!=Plan.console_in||t->StandardErrorHandle!=Plan.console_err||
    t->ConIn!=Plan.keys||t->ConOut!=Plan.text||t->StdErr!=Plan.err||!t->ConIn||(UINTN)t->ConIn->ReadKeyStroke!=Plan.key_read;
  if(log){
    BOOLEAN out=t->ConsoleOutHandle!=Plan.console_out,in=t->ConsoleInHandle!=Plan.console_in,err=t->StandardErrorHandle!=Plan.console_err;
    BOOLEAN keys=t->ConIn!=Plan.keys,text=t->ConOut!=Plan.text,errtext=t->StdErr!=Plan.err;
    UINTN key_read=t->ConIn?(UINTN)t->ConIn->ReadKeyStroke:0;
    BOOLEAN read=!t->ConIn||key_read!=Plan.key_read;
    NOTE("preflight console: changed=%u out_handle=%u in_handle=%u err_handle=%u keys=%u text=%u stderr=%u key_read=%u\n",changed,out,in,err,keys,text,errtext,read);
    if(changed)NOTE("preflight console identities: out=%#llx/%#llx in=%#llx/%#llx err=%#llx/%#llx keys=%#llx/%#llx text=%#llx/%#llx stderr=%#llx/%#llx read=%#llx/%#llx (expected/current)\n",
      (unsigned long long)(UINTN)Plan.console_out,(unsigned long long)(UINTN)t->ConsoleOutHandle,
      (unsigned long long)(UINTN)Plan.console_in,(unsigned long long)(UINTN)t->ConsoleInHandle,
      (unsigned long long)(UINTN)Plan.console_err,(unsigned long long)(UINTN)t->StandardErrorHandle,
      (unsigned long long)(UINTN)Plan.keys,(unsigned long long)(UINTN)t->ConIn,
      (unsigned long long)(UINTN)Plan.text,(unsigned long long)(UINTN)t->ConOut,
      (unsigned long long)(UINTN)Plan.err,(unsigned long long)(UINTN)t->StdErr,
      (unsigned long long)Plan.key_read,(unsigned long long)key_read);
  }
  return changed?EFI_NOT_READY:EFI_SUCCESS;
}
static EFI_STATUS Alive(VOID){return AliveChecked(FALSE);}
static EFI_STATUS ReadConfig(UINT32 *c) {
  for(UINTN i=0;i<64;i++)if(EFI_ERROR(GuConfigRead(EfiPciIoWidthUint32,(UINT32)i*4,&c[i])))return EFI_DEVICE_ERROR;
  return EFI_SUCCESS;
}
/* Status and the PCIe device status register are volatile (RW1C error bits); everything
   else, including command, BARs, ROM and capability control, must match. Command bit 2 (bus
   master) is masked here on both sides: it is judged explicitly (bme_entry, ClearBme), not as drift. */
static BOOLEAN SameConfig(const UINT32 *a,const UINT32 *b,BOOLEAN log) {
  BOOLEAN same=TRUE;
  for(UINTN i=0;i<64;i++) {
    UINT32 x=a[i]^b[i];
    if(i==1)x&=0xfffbU;
    if(Gu.pcie_cap&&i==(UINTN)(Gu.pcie_cap+8)/4)x&=0xffffU;
    if(x){same=FALSE;if(log)NOTE("config drift: offset=%#x expected=%#x now=%#x\n",(unsigned)(i*4),b[i],a[i]);}
  }
  return same;
}
/* With the firmware driver running again it may legitimately rewrite device control and
   similar registers: judge identity, command and BARs. A driver that sets bus master again
   is accepted only on a board whose firmware had it set at entry (Plan.bme_entry); decode
   rules are unchanged. */
static BOOLEAN SameAfterDriver(const UINT32 *c) {
  if(c[0]!=Plan.config[0]||c[2]!=Plan.config[2]||c[11]!=Plan.config[11])return FALSE;
  if((c[1]&4)&&!Plan.bme_entry)return FALSE;
  /* Decode bits are judged against the firmware's entry command as well: this image may have had to
     enable memory decode itself on a hybrid laptop, and the driver need not put that back. */
  if((c[1]&0xfffbU)!=(Plan.config[1]&0xfffbU)&&(UINT16)(c[1]&0xffffU)!=(UINT16)(Plan.command_entry&0xfffbU))return FALSE;
  for(UINTN i=4;i<=9;i++)if(c[i]!=Plan.config[i])return FALSE;
  return TRUE;
}
static EFI_STATUS Bar(VOID) {
  EFI_ACPI_ADDRESS_SPACE_DESCRIPTOR *d=NULL;UINT64 support=0;
  if(!Gu.pci||!Gu.pci->GetBarAttributes)return EFI_UNSUPPORTED;
  EFI_STATUS s=Gu.pci->GetBarAttributes(Gu.pci,0,&support,(VOID **)&d);
  /* A 32-bit memory BAR of exactly 16 MiB; its address is whatever this firmware assigned. */
  if(s==EFI_SUCCESS&&(!d||d->Desc!=0x8a||d->Len!=43||d->ResType||d->AddrTranslationOffset||
     d->AddrLen!=GU_BAR0_BYTES||d->AddrRangeMin!=Gu.bar_base||d->AddrRangeMin>0xffffffffULL||(d->AddrRangeMin&(GU_BAR0_BYTES-1))))s=EFI_UNSUPPORTED;
  if(d&&Gu.bs->FreePool(d)!=EFI_SUCCESS)s=EFI_DEVICE_ERROR;
  return s;
}
EFI_STATUS GuRelPreflight(EFI_SYSTEM_TABLE *t,EFI_HANDLE self,EFI_HANDLE pci) {
  if(Plan.mutated||Plan.ready)return EFI_ALREADY_STARTED;
  memset(&Plan,0,sizeof(Plan));Plan.table=t;Plan.self=self;Plan.pci=pci;
  if(!t||!t->BootServices||!self||!pci||Gu.handle!=pci||Gu.image!=self||Gu.bs!=t->BootServices||
     Gu.started||Gu.owned||Gu.armed||!Gu.located)return EFI_INVALID_PARAMETER;
  EFI_BOOT_SERVICES *b=t->BootServices;
  if(!b->DisconnectController||!b->ConnectController||!b->OpenProtocol||!b->CloseProtocol||!b->RaiseTPL||!b->RestoreTPL||
     !b->ProtocolsPerHandle||!b->OpenProtocolInformation||!b->LocateHandleBuffer||!b->HandleProtocol||!b->LocateDevicePath)return EFI_UNSUPPORTED;
  Plan.console_out=t->ConsoleOutHandle;Plan.console_in=t->ConsoleInHandle;Plan.console_err=t->StandardErrorHandle;
  Plan.text=t->ConOut;Plan.err=t->StdErr;Plan.keys=t->ConIn;
  if(!Plan.console_out||!Plan.console_in||!Plan.console_err||!Plan.text||!Plan.err||!Plan.keys||!Plan.keys->ReadKeyStroke)return EFI_UNSUPPORTED;
  Plan.key_read=(UINTN)Plan.keys->ReadKeyStroke;
  NOTE("preflight console snapshot: out_handle=%#llx in_handle=%#llx err_handle=%#llx keys=%#llx text=%#llx stderr=%#llx read=%#llx\n",
    (unsigned long long)(UINTN)Plan.console_out,(unsigned long long)(UINTN)Plan.console_in,(unsigned long long)(UINTN)Plan.console_err,
    (unsigned long long)(UINTN)Plan.keys,(unsigned long long)(UINTN)Plan.text,(unsigned long long)(UINTN)Plan.err,(unsigned long long)Plan.key_read);
  UINTN seg,bus,dev,fun;EFI_STATUS s=Gu.pci->GetLocation(Gu.pci,&seg,&bus,&dev,&fun);
  if(s==EFI_SUCCESS)s=ReadConfig(Plan.config);
  if(s==EFI_SUCCESS&&!GuTargetConfig(Plan.config,seg,bus,dev,fun))s=EFI_UNSUPPORTED;
  /* A hybrid-graphics laptop enters UEFI with memory decode clear while the parent bridge already
     decodes the BAR (seen on a GA106M board). Enable MEMORY through PciIo before the ownership checks
     so the command register and the cached attributes agree; the entry command is kept so the
     post-driver comparison still judges the firmware's own state. */
  if(s==EFI_SUCCESS)Plan.command_entry=Gu.entry_command;
  if(s==EFI_SUCCESS&&!(Plan.config[1]&2)) {
    if(!Gu.pci->Attributes)s=EFI_UNSUPPORTED;
    else {
      EFI_STATUS enabled=Gu.pci->Attributes(Gu.pci,EfiPciIoAttributeOperationEnable,EFI_PCI_IO_ATTRIBUTE_MEMORY,NULL);
      if(EFI_ERROR(enabled))s=enabled;
      else if(EFI_ERROR(ReadConfig(Plan.config))||!(Plan.config[1]&2))s=EFI_NOT_READY;
      NOTE("memory decode forced: status=%#llx entry_command=%#x command=%#x\n",(unsigned long long)enabled,
        (unsigned)Plan.command_entry,EFI_ERROR(s)?0:(unsigned)(Plan.config[1]&0xffffU));
    }
  }
  /* Board firmware may leave bus master set before any driver binds; it is cleared after the claim, as the Linux module does. */
  Plan.bme_entry=(Plan.config[1]&4)!=0;
  if(s==EFI_SUCCESS)s=Gu.pci->Attributes?Gu.pci->Attributes(Gu.pci,EfiPciIoAttributeOperationGet,0,&Plan.attributes):EFI_UNSUPPORTED;
  /* The firmware PciIo may cache an IO attribute the command register does not have, and may or may not cache
     a bus master the board firmware set directly: only memory decode is required here. */
  if(s==EFI_SUCCESS&&!(Plan.attributes&EFI_PCI_IO_ATTRIBUTE_MEMORY))s=EFI_NOT_READY;
  if(s==EFI_SUCCESS)s=Bar();
  if(s==EFI_SUCCESS)s=FindOwner(&Plan.owner,TRUE);
  if(s==EFI_SUCCESS&&!GopsChecked(TRUE,TRUE)){
    s=EFI_NOT_READY; /* fixed before the independent survey: its results cannot admit the card */
    SurveyGopsAfterRefusal();
  }
  if(s==EFI_SUCCESS&&AliveChecked(TRUE)!=EFI_SUCCESS)s=EFI_NOT_READY;
  if(s==EFI_SUCCESS)NOTE("release preflight: slot=%zu:%zu:%zu.%zu bar0=%#llx attributes=%#llx driver=%u display_children=%zu bme_entry=%u\n",
    seg,bus,dev,fun,(unsigned long long)Gu.bar_base,(unsigned long long)Plan.attributes,Plan.owner.agent!=NULL,(size_t)Plan.owner.child_count,Plan.bme_entry);
  for(UINTN i=0;s==EFI_SUCCESS&&i<Plan.owner.child_count;i++){
    const CHILD *c=&Plan.owner.children[i];
    NOTE("display child[%u]: %s gop=%u %ux%u stride=%u format=%u fb=%#llx size=%#llx\n",(unsigned)i,c->screen?"screen":"no screen",
      c->gop!=NULL,c->width,c->height,c->stride,c->format,(unsigned long long)c->framebuffer,(unsigned long long)c->framebuffer_size);
  }
  NOTE("release preflight: status=%#llx\n",(unsigned long long)s);
  if(s==EFI_SUCCESS)Plan.ready=TRUE;
  return s;
}
/* Exclusive claim: every record on the GPU handle must be passive when it is taken. */
static EFI_STATUS Claim(VOID) {
  RECORD records[MAX_RECORDS];UINTN count=0;
  EFI_TPL old=Gu.bs->RaiseTPL(TPL_NOTIFY);
  EFI_STATUS s=Snapshot(records,&count);
  if(!EFI_ERROR(s))for(UINTN i=0;i<count;i++)if(!Passive(records[i].entry.Attributes))s=EFI_ACCESS_DENIED;
  if(!EFI_ERROR(s)) {
    EFI_PCI_IO_PROTOCOL *pci=NULL;
    s=Gu.bs->OpenProtocol(Gu.handle,&PciGuid,(VOID **)&pci,Gu.image,NULL,EFI_OPEN_PROTOCOL_EXCLUSIVE);
    if(!EFI_ERROR(s)){Plan.claimed=TRUE;Gu.owned=TRUE;if(pci!=Gu.pci)s=EFI_COMPROMISED_DATA;}
  }
  Gu.bs->RestoreTPL(old);LogRecords(records,count,s);return s;
}
/* The driver's Stop may clear IO/MEM decode. Restore only bits that were set at preflight and
   are now clear, and only if nothing else in config space moved. Never enables bus master. */
static EFI_STATUS RestoreDecode(VOID) {
  UINT32 now[64],normalized[64],after[64];
  if(!Gu.pci||!Gu.owned||Gu.started||Gu.allocations||Gu.dma_count||Gu.fault||Gu.retained)return EFI_ACCESS_DENIED;
  EFI_STATUS s=ReadConfig(now);if(EFI_ERROR(s))return s;
  UINT32 missing=Plan.config[1]&~now[1]&3U;
  memcpy(normalized,now,sizeof(normalized));normalized[1]|=missing;
  if(!SameConfig(normalized,Plan.config,TRUE)){NOTE("decode restore refused: config differs beyond cleared original IO/MEM bits\n");return EFI_UNSUPPORTED;}
  if(!missing){NOTE("decode restore not needed\n");return EFI_SUCCESS;}
  UINT64 needed=(missing&1?EFI_PCI_IO_ATTRIBUTE_IO:0)|(missing&2?EFI_PCI_IO_ATTRIBUTE_MEMORY:0),supported=0;
  if(!Gu.pci->Attributes)return EFI_UNSUPPORTED;
  s=Gu.pci->Attributes(Gu.pci,EfiPciIoAttributeOperationSupported,0,&supported);
  if(EFI_ERROR(s)||(supported&needed)!=needed)return EFI_ERROR(s)?s:EFI_UNSUPPORTED;
  NOTE("decode restore intent: saved_command=%#x current_command=%#x missing=%#x\n",Plan.config[1]&0xffff,now[1]&0xffff,missing);
  if(!GuBootLogOpen()||Gu.fault)return EFI_DEVICE_ERROR;
  EFI_STATUS enabled=Gu.pci->Attributes(Gu.pci,EfiPciIoAttributeOperationEnable,needed,NULL);
  NOTE("decode enable status=%#llx\n",(unsigned long long)enabled);
  s=ReadConfig(after);
  BOOLEAN matched=!EFI_ERROR(s)&&SameConfig(after,Plan.config,TRUE);
  if(EFI_ERROR(enabled))return enabled;
  if(EFI_ERROR(s))return s;
  return matched&&!Gu.fault?EFI_SUCCESS:EFI_COMPROMISED_DATA;
}
/* Board firmware may leave PCI bus master set before any driver binds; the Linux module clears it when it
   claims the card ("claim: cleared firmware BME"). A PCI command-register change through PciIo, the same
   class of write as RestoreDecode: no MMIO, no GPU register. Cleared if either the command register or the
   cached attribute has it. Nothing else may change (volatile status aside). On success the baselines every
   later strict comparison uses are BME-clear. */
static EFI_STATUS ClearBme(VOID) {
  UINT32 now[64],after[64];UINT64 before=0,cached=0;
  if(!Gu.pci||!Gu.owned||Gu.started||Gu.allocations||Gu.dma_count||Gu.fault||Gu.retained||!Gu.pci->Attributes)return EFI_ACCESS_DENIED;
  EFI_STATUS s=ReadConfig(now);
  if(!EFI_ERROR(s))s=Gu.pci->Attributes(Gu.pci,EfiPciIoAttributeOperationGet,0,&before);
  if(EFI_ERROR(s))return s;
  if((now[1]&4)||(before&EFI_PCI_IO_ATTRIBUTE_BUS_MASTER)) {
    NOTE("claim: clearing firmware BME: command=%#x attributes=%#llx at_entry=%u\n",now[1]&0xffff,(unsigned long long)before,Plan.bme_entry);
    if(!GuBootLogOpen()||Gu.fault)return EFI_DEVICE_ERROR;
    EFI_STATUS cleared=Gu.pci->Attributes(Gu.pci,EfiPciIoAttributeOperationDisable,EFI_PCI_IO_ATTRIBUTE_BUS_MASTER,NULL);
    s=ReadConfig(after);
    if(!EFI_ERROR(s))s=Gu.pci->Attributes(Gu.pci,EfiPciIoAttributeOperationGet,0,&cached);
    NOTE("claim: cleared firmware BME: status=%#llx command=%#x attributes=%#llx\n",(unsigned long long)cleared,
      EFI_ERROR(s)?0xffffU:after[1]&0xffff,(unsigned long long)cached);
    if(EFI_ERROR(cleared))return cleared;
    if(EFI_ERROR(s))return s;
    if((after[1]&4)||(cached&EFI_PCI_IO_ATTRIBUTE_BUS_MASTER)||!SameConfig(after,now,TRUE))return EFI_COMPROMISED_DATA;
  }
  Plan.config[1]&=~4U;Plan.attributes&=~(UINT64)EFI_PCI_IO_ATTRIBUTE_BUS_MASTER;
  return EFI_SUCCESS;
}
/* Fresh PciIo interface for the same card in the same slot (after a driver stops or starts). */
static EFI_STATUS Refresh(VOID) {
  EFI_PCI_IO_PROTOCOL *fresh=NULL;UINTN seg,bus,dev,fun;UINT32 c[64]={0};
  Gu.pci=NULL;
  EFI_STATUS s=Gu.bs->HandleProtocol(Gu.handle,&PciGuid,(VOID **)&fresh);
  if(EFI_ERROR(s)||!fresh||!fresh->GetLocation||!fresh->Pci.Read||!fresh->Pci.Write)return EFI_NOT_FOUND;
  s=fresh->GetLocation(fresh,&seg,&bus,&dev,&fun);if(EFI_ERROR(s))return s;
  static const UINT32 offsets[]={0,8,12};
  for(UINTN i=0;i<3;i++){s=fresh->Pci.Read(fresh,EfiPciIoWidthUint32,offsets[i],1,&c[offsets[i]/4]);if(EFI_ERROR(s))return s;}
  if(!GuTargetConfig(c,seg,bus,dev,fun))return EFI_UNSUPPORTED;
  Gu.pci=fresh;return EFI_SUCCESS;
}
EFI_STATUS GuRelRelease(VOID) {
  if(!Plan.ready||Plan.mutated||Gu.started||Gu.owned||Gu.fault||!Gu.profile_verified||!Gu.prom_verified)return EFI_NOT_READY;
  GuBootSilence();
  NOTE("release: intent; stopping the GPU's firmware driver once\n");
  if(!GuBootLogOpen()||Gu.fault){GuBootUnsilence();return EFI_DEVICE_ERROR;} /* nothing released yet: keep the console usable */
  /* Durable intent first; no file I/O between the last snapshot comparison and DisconnectController. */
  OWNER now;UINT32 c[64];
  EFI_STATUS s=FindOwner(&now,FALSE);
  if(s==EFI_SUCCESS&&!SameOwner(&Plan.owner,&now))s=EFI_ABORTED;
  if(s==EFI_SUCCESS)s=Alive();
  if(s==EFI_SUCCESS)s=ReadConfig(c);
  if(s==EFI_SUCCESS&&!SameConfig(c,Plan.config,FALSE))s=EFI_NOT_READY;
  if(s==EFI_SUCCESS&&(c[1]&4)&&!Plan.bme_entry)s=EFI_NOT_READY; /* bus master appeared since preflight */
  if(s==EFI_SUCCESS&&!GuAd104ColdEntry())s=EFI_NOT_READY;
  if(s==EFI_SUCCESS&&!Gops(TRUE))s=EFI_NOT_READY;
  if(s!=EFI_SUCCESS||Gu.fault){GuBootUnsilence();return s==EFI_SUCCESS?EFI_DEVICE_ERROR:s;}
  EFI_PCI_IO_PROTOCOL *prior=Gu.pci;EFI_STATUS released=EFI_SUCCESS,refreshed=EFI_SUCCESS;
  if(Plan.owner.agent) {
    Plan.mutated=TRUE; /* recorded before the callback: an error may follow a partial stop */
    Gu.pci=NULL;
    released=Gu.bs->DisconnectController(Gu.handle,Plan.owner.agent,NULL);
    EFI_TPL old=Gu.bs->RaiseTPL(TPL_NOTIFY);refreshed=Refresh();Gu.bs->RestoreTPL(old);
  } else Plan.mutated=TRUE;
  NOTE("driver release: status=%#llx refresh=%#llx same_pci=%u\n",(unsigned long long)released,(unsigned long long)refreshed,Gu.pci==prior);
  s=EFI_ERROR(released)?released:EFI_ERROR(refreshed)?refreshed:Gu.pci!=prior?EFI_COMPROMISED_DATA:EFI_SUCCESS;
  if(s==EFI_SUCCESS)s=Claim();
  if(s==EFI_SUCCESS&&!Gops(FALSE))s=EFI_NOT_READY;
  if(s==EFI_SUCCESS)s=RestoreDecode();
  if(s==EFI_SUCCESS)s=ClearBme();
  if(s==EFI_SUCCESS){s=ReadConfig(c);if(s==EFI_SUCCESS&&!SameConfig(c,Plan.config,TRUE))s=EFI_NOT_READY;}
  if(s==EFI_SUCCESS){UINT64 a=0;s=Gu.pci->Attributes(Gu.pci,EfiPciIoAttributeOperationGet,0,&a);
    const UINT64 m=EFI_PCI_IO_ATTRIBUTE_MEMORY|EFI_PCI_IO_ATTRIBUTE_BUS_MASTER;
    if(s==EFI_SUCCESS&&(a&m)!=(Plan.attributes&m)){NOTE("attributes after release: %#llx expected(mem,bm)=%#llx\n",(unsigned long long)a,(unsigned long long)(Plan.attributes&m));s=EFI_NOT_READY;}}
  if(s==EFI_SUCCESS)s=Bar();
  if(s==EFI_SUCCESS&&!GuAd104ColdEntry())s=EFI_NOT_READY;
  NOTE("release: status=%#llx\n",(unsigned long long)s);
  return s!=EFI_SUCCESS||Gu.fault?(s==EFI_SUCCESS?EFI_DEVICE_ERROR:s):EFI_SUCCESS;
}
BOOLEAN GuRelReleased(VOID) {
  UINT32 c[64];const char *failed=NULL;
  if(!Plan.ready||!Plan.mutated||!Plan.claimed||!Gu.owned||Gu.fault)failed="state";
  else if(Alive()!=EFI_SUCCESS)failed="console";
  else if(!Gops(FALSE))failed="GOP";
  else if(ReadConfig(c)!=EFI_SUCCESS)failed="config-read";
  else if(!SameConfig(c,Plan.config,FALSE))failed="config-drift";
  if(failed)NOTE("release check failed: %s fault=%u flrs=%u\n",failed,Gu.fault,Gu.flrs);
  return !failed;
}
/* Close the claim and connect the same driver again; shared by Finish and Recover. */
static EFI_STATUS Reconnect(BOOLEAN *gop) {
  UINT32 c[64];*gop=FALSE;
  if(Gu.owned) {
    EFI_STATUS s=Gu.bs->CloseProtocol(Gu.handle,&PciGuid,Gu.image,NULL);
    NOTE("claim close: status=%#llx\n",(unsigned long long)s);
    if(EFI_ERROR(s))return s;
    Plan.claimed=FALSE;Gu.owned=FALSE;
  }
  EFI_STATUS s=EFI_SUCCESS;
  if(Plan.owner.agent) {
    EFI_HANDLE drivers[2]={Plan.owner.agent,NULL};
    s=Gu.bs->ConnectController(Gu.handle,drivers,NULL,TRUE);
    NOTE("ConnectController: status=%#llx\n",(unsigned long long)s);
    if(EFI_ERROR(s))return s;
  }
  EFI_TPL old=Gu.bs->RaiseTPL(TPL_NOTIFY);s=Refresh();Gu.bs->RestoreTPL(old);
  if(EFI_ERROR(s))return s;
  *gop=Gops(TRUE);
  s=ReadConfig(c);
  /* After reconnect the command register must be the original one and bus master clear. */
  if(!EFI_ERROR(s)&&!SameAfterDriver(c)){SameConfig(c,Plan.config,TRUE);s=EFI_NOT_READY;}
  if(!*gop)NOTE("GOP did not come back (children expected=%zu)\n",(size_t)Plan.owner.child_count);
  return s;
}
EFI_STATUS GuRelFinish(BOOLEAN *gop) {
  *gop=FALSE;
  if(!Plan.mutated||!Plan.claimed||!Gu.owned||Gu.fault||!GuSafeToReturn()||!Gu.quiesced||Gu.flrs!=1)return EFI_NOT_READY;
  UINT32 ss0=GuRead32(0x82381c),ss1=GuRead32(0x823820);
  NOTE("POST-FLR SS0=%#x SS1=%#x unlock_matched=%u\n",ss0,ss1,ss0==0x88888888&&ss1==8);
  if(Gu.fault||ss0==0xffffffff||ss1==0xffffffff||(ss0&0xffff0000)==0xbadf0000)return EFI_DEVICE_ERROR;
  NOTE("stage=before_GOP_reconnect; transaction quiesced, DMA released, PCI restored\n");
  if(!GuBootLogOpen()||Gu.fault)return EFI_DEVICE_ERROR;
  EFI_STATUS s=Reconnect(gop);
  if(!EFI_ERROR(s)){ss0=GuRead32(0x82381c);ss1=GuRead32(0x823820);NOTE("POST-GOP SS0=%#x SS1=%#x\n",ss0,ss1);if(Gu.fault||ss0==0xffffffff||ss1==0xffffffff)s=EFI_DEVICE_ERROR;}
  if(*gop)GuBootUnsilence();
  return s;
}
EFI_STATUS GuRelRecover(BOOLEAN *gop) {
  *gop=FALSE;
  if(!Plan.ready||!Plan.mutated||Gu.started||Gu.mmio_writes||Gu.flrs||Gu.dma_count||Gu.allocations||Gu.master_attributes_pending)return EFI_NOT_READY;
  EFI_STATUS s=Reconnect(gop);
  if(*gop)GuBootUnsilence();
  return s;
}
BOOLEAN GuRelReadyForWindows(BOOLEAN unlocked) {
  if(!Plan.ready||!Plan.mutated||Plan.claimed||Gu.owned||Gu.fault||!GuSafeToReturn())return FALSE;
  if(unlocked?(!Gu.quiesced||Gu.flrs!=1):(Gu.started||Gu.flrs))return FALSE;
  UINT32 c[64];
  if(Alive()!=EFI_SUCCESS||!Gops(TRUE)||ReadConfig(c)!=EFI_SUCCESS||!SameAfterDriver(c))return FALSE;
  UINT32 chip=GuRead32(0),cpu=GuRead32(0x110100),hi=GuRead32(0x1fa828);
  UINT32 ss0=GuRead32(0x82381c),ss1=GuRead32(0x823820),readout=GuRead32(0x823818),plm=GuRead32(0x823804);
  if(Gu.fault||chip==0xffffffff||(chip&0xffff0000)==0xbadf0000||cpu==0xffffffff||(cpu&0xffff0000)==0xbadf0000)return FALSE;
  /* The state the Linux module verified on this card: PLM open, SS0 88888888, SS1 8, READOUT_1
     clear. Falcon and WPR2 state are not part of that criterion; GuRelFinish logs them. */
  (void)cpu;(void)hi;
  if(unlocked)return ss0==0x88888888&&ss1==8&&!readout&&plm==0xffffffff;
  return plm!=0xffffffff&&ss0!=0x88888888;
}
BOOLEAN GuRelMutated(VOID){return Plan.mutated;}
