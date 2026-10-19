import Leanux.Proofs.WG.Progress.FsDescriptorFiniteSource
import Leanux.Proofs.WG.Progress.FsAnonymousFiniteSource
import Leanux.FS.Eventpoll

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.FsFinite
open Leanux

/-! Finite epoll creation and registration allocation callers, with the
original quota, publication, descriptor cleanup and refusal paths. -/

def epAlloc : FS.M (Except Int EpId) := do
  if ← branch .epAllocNoMem (!(← (monadLift (hiddenAllocFinite .kzallocEp)))) then return .error (-ENOMEM)
  -- mutex_init, spin_lock_init, seqcount_spinlock_init, init_waitqueue_head x2,
  -- INIT_LIST_HEAD(&ep->rdllist), ep->rbr = RB_ROOT_CACHED, ep->ovflist = EP_UNACTIVE_PTR
  refcountIncGuestWide .rootUserCount   -- ep->user = get_current_user()
  -- refcount_set(&ep->refcount, 1)
  let id := (← get).nextEp
  setEp id {}
  modify fun k => { k with nextEp := id + 1 }
  return .ok id

theorem epAlloc_source :
    Leanux.epAlloc = epAlloc := by
  unfold Leanux.epAlloc epAlloc
  simp only [hiddenAlloc, hiddenAlloc_finite_source] <;> rfl

def epAttachFile (fid : FileId) (epiId : EpiId) : FS.M Int := do
  let file ← getFile fid
  let ep ← if ← branch .epAttachFileIsEpoll (isFileEpoll file) then some <$> epOf file else pure none
  let mut head : Option FEp := none
  let mut toFree := false
  if ← branch .epAttachFileEp ep.isSome then
    head := some (.epRefs ep.get!)
  else if ← branch .epAttachFileNoFEp (file.fEp == .null) then
    -- allocate: to_free = kmem_cache_zalloc(ephead_cache, GFP_KERNEL)
    if ← branch .epAttachFileHeadNoMem (!(← (monadLift (hiddenAllocFinite .kmemCacheZallocEphead)))) then return -ENOMEM
    toFree := true
    head := some (.head [])
  -- spin_lock(&file->f_lock)
  let file ← getFile fid
  if ← branch .epAttachFileFEpNull (file.fEp == .null) then
    match head with
    | none =>
      _ ← branch .epAttachFileRace true
      invariant "ep_attach_file: f_ep NULL under the lock with no head (a concurrent attach)"
    | some h =>
      _ ← branch .epAttachFileRace false
      setFile fid { file with fEp := h }   -- WRITE_ONCE(file->f_ep, head)
      toFree := false
  -- hlist_add_head_rcu(&epi->fllink, file->f_ep)
  let file ← getFile fid
  match file.fEp with
  | .head items => setFile fid { file with fEp := .head (epiId :: items) }
  | .epRefs e => setEp e { (← getEp e) with refs := epiId :: (← getEp e).refs }
  | .null => invariant "ep_attach_file: f_ep NULL after the install"
  -- spin_unlock(&file->f_lock)
  freeEphead toFree
  return 0

theorem epAttachFile_source (fid : FileId) (epiId : EpiId) :
    Leanux.epAttachFile fid epiId = epAttachFile fid epiId := by
  unfold Leanux.epAttachFile epAttachFile
  simp only [hiddenAlloc, hiddenAlloc_finite_source] <;> rfl

def epAllocEpitem (ep : EpId) (event : EpollEvent) (tfile : FileId) (fd : Int) : FS.M (Except Int EpiId) := do
  let k ← get
  let count := k.user.epollWatches
  let max := k.maxUserWatches
  let cmp : Int ← do
    if ← branch .percpuCounterCompareGt (count > max) then pure 1   -- folded into the `<` below
    else if ← branchCmp .percpuCounterCompareLt (count < max) count max then pure (-1)
    else pure 0
  if ← branch .epAllocEpitemOverWatches (cmp >= 0) then return .error (-ENOSPC)
  modify fun k => { k with user := { k.user with epollWatches := k.user.epollWatches + 1 } }
  if ← branch .epAllocEpitemNoMem (!(← (monadLift (hiddenAllocFinite .kmemCacheZallocEpi)))) then
    modify fun k => { k with user := { k.user with epollWatches := k.user.epollWatches - 1 } }
    return .error (-ENOMEM)
  -- INIT_LIST_HEAD(&epi->rdllink); epi->ep = ep; ep_set_ffd; epi->event = *event; epi_clear_ovflist
  let id := (← get).nextEpi
  setEpi id { ep, file := tfile, fd, fileAddr := 0, events := event.events, data := event.data }
  modify fun k => { k with nextEpi := id + 1 }
  return .ok id

theorem epAllocEpitem_source (ep : EpId) (event : EpollEvent) (tfile : FileId) (fd : Int) :
    Leanux.epAllocEpitem ep event tfile fd = epAllocEpitem ep event tfile fd := by
  unfold Leanux.epAllocEpitem epAllocEpitem
  simp only [hiddenAlloc, hiddenAlloc_finite_source] <;> rfl

def epRegisterEpitem (ep : EpId) (epiId : EpiId) (tep : Option EpId) (fullCheck : Bool) : FS.M Int := do
  let tfile := (← getEpi epiId).file
  if ← branch .epRegisterEpitemTep tep.isSome then pure ()   -- mutex_lock_nested(&tep->mtx, 1)
  let error ← epAttachFile tfile epiId
  if ← branch .epRegisterEpitemAttachError (error != 0) then
    if ← branch .epRegisterEpitemAttachErrorTep tep.isSome then pure ()   -- mutex_unlock(&tep->mtx)
    freeEpi epiId   -- kmem_cache_free(epi_cache, epi)
    modify fun k => { k with user := { k.user with epollWatches := k.user.epollWatches - 1 } }
    return error
  if ← branchCmp .epRegisterEpitemFullCheck fullCheck (if fullCheck then 1 else 0) 0 then
    if ← branch .epRegisterEpitemNotTep tep.isNone then listFile tfile
  epRbtreeInsert ep epiId
  if ← branch .epRegisterEpitemTepUnlock tep.isSome then pure ()   -- mutex_unlock(&tep->mtx)
  epGet ep
  return 0

theorem epRegisterEpitem_source (ep : EpId) (epiId : EpiId) (tep : Option EpId) (fullCheck : Bool) :
    Leanux.epRegisterEpitem ep epiId tep fullCheck = epRegisterEpitem ep epiId tep fullCheck := by
  unfold Leanux.epRegisterEpitem epRegisterEpitem
  simp only [epAttachFile_source] <;> rfl

def doEpollCreate (flags : UInt32) : FS.M Int := do
  if ← branchCmp .doEpollCreateInvalidFlags (flags &&& ~~~EPOLL_CLOEXEC != 0) (flags &&& ~~~EPOLL_CLOEXEC).toNat 0 then
    return -EINVAL
  let r ← epAlloc
  if ← branch .doEpollCreateAllocError (r matches .error _) then
    return match r with | .error e => e | .ok _ => 0
  let .ok ep := r | invariant "unreachable"
  let fd ← getUnusedFdFlags (O_RDWR ||| (flags &&& O_CLOEXEC))
  if ← branchCmp .doEpollCreateFdError (fd < 0) fd 0 then
    epClearAndPut ep   -- out_free_ep
    return fd
  let file ← anonInodeGetfile .eventpoll (.eventpoll ep) (O_RDWR ||| (flags &&& O_CLOEXEC))
  if ← branch .doEpollCreateFileError (file matches .error _) then
    putUnusedFd fd.toNat   -- out_free_fd
    epClearAndPut ep       -- out_free_ep
    return match file with | .error e => e | .ok _ => 0
  let .ok fid := file | invariant "unreachable"
  setEp ep { (← getEp ep) with file := some fid }   -- ep->file = file
  fdInstall fd.toNat fid
  return fd

theorem doEpollCreate_source (flags : UInt32) :
    Leanux.doEpollCreate flags = doEpollCreate flags := by
  unfold Leanux.doEpollCreate doEpollCreate
  simp only [epAlloc_source, getUnusedFdFlags_source, anonInodeGetfile_source] <;> rfl

def sysEpollCreate1 (flags : UInt32) : FS.M Int := doEpollCreate flags

theorem sysEpollCreate1_source (flags : UInt32) :
    Leanux.sysEpollCreate1 flags = sysEpollCreate1 flags := by
  unfold Leanux.sysEpollCreate1 sysEpollCreate1
  simp only [doEpollCreate_source] <;> rfl


end Leanux.Proofs.WG.Progress.FsFinite
