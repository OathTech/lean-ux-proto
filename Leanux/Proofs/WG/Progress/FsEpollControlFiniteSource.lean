import Leanux.Proofs.WG.Progress.FsEpollAllocationFiniteSource
import Leanux.Proofs.WG.Progress.FsEpollPollFiniteSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.FsFinite
open Leanux

/-! Native insertion/modification and epoll_ctl using the finite poll
and allocation callers. The private control body has one callback seam. -/

def epInsert (ep : EpId) (event : EpollEvent) (tfile : FileId) (fd : Int) (fullCheck : Bool) : FS.M Int := do
  let tf ← getFile tfile
  let tep ← if ← branch .epInsertTargetEpoll (isFileEpoll tf) then some <$> epOf tf else pure none
  let r ← epAllocEpitem ep event tfile fd
  if ← branch .epInsertAllocError (r matches .error _) then
    return match r with | .error e => e | .ok _ => 0
  let .ok epiId := r | invariant "unreachable"
  let error ← epRegisterEpitem ep epiId tep fullCheck
  if ← branch .epInsertRegisterError (error != 0) then return error
  -- `full_check && reverse_path_check()`
  let tooMany ← do
    if ← branchCmp .epInsertFullCheck fullCheck (if fullCheck then 1 else 0) 0 then
      branch .epInsertReversePathFailed ((← reversePathCheck) != 0)
    else pure false
  if tooMany then
    epRemove ep epiId
    return -EINVAL
  let epi ← getEpi epiId
  if ← branchCmp .epInsertWakeup (hasFlag epi.events EPOLLWAKEUP) (epi.events &&& EPOLLWAKEUP).toNat 0 then
    unsupported "ep_create_wakeup_source: EPOLLWAKEUP survived ep_take_care_of_epollwakeup"
  -- epq.epi = epi; init_poll_funcptr(&epq.pt, ep_ptable_queue_proc)
  modify fun k => { k with epqEpi := some epiId }
  let revents ← epItemPollAt epiId { qproc := some epiId } 1
  -- ep_ptable_queue_proc() signals allocation failure by clearing epq.epi
  if ← branch .epInsertPwqAllocFailed (← get).epqEpi.isNone then
    epRemove ep epiId
    return -ENOMEM
  modify fun k => { k with epqEpi := none }   -- epq leaves scope
  -- spin_lock_irq(&ep->lock)
  epSetBusyPollNapiId epiId
  let epi ← getEpi epiId
  let ready ← do
    if ← branchCmp .epInsertReady (revents != 0) revents.toNat 0 then branch .epInsertNotLinked (!epi.linked)
    else pure false
  let mut pwake := 0
  if ready then
    -- list_add_tail(&epi->rdllink, &ep->rdllist); ep_pm_stay_awake (empty)
    let e ← getEp ep
    setEp ep { e with rdllist := e.rdllist ++ [epiId] }
    setEpi epiId { epi with linked := true }
    if ← branch .epInsertWqActive (← waitqueueActive (.epWq ep)) then
      unsupported "wake_up(&ep->wq) at ep_insert: a task sleeping in epoll_wait (tier 2)"
    if ← branch .epInsertPollWaitActive (← waitqueueActive (.epPollWait ep)) then pwake := pwake + 1
  -- spin_unlock_irq(&ep->lock)
  if ← branch .epInsertPwake (pwake != 0) then epPollSafewake ep none 0
  return 0

theorem epInsert_source (ep : EpId) (event : EpollEvent) (tfile : FileId) (fd : Int) (fullCheck : Bool) :
    Leanux.epInsert ep event tfile fd fullCheck = epInsert ep event tfile fd fullCheck := by
  unfold Leanux.epInsert epInsert
  simp only [epAllocEpitem_source, epRegisterEpitem_source, epItemPollAt_source] <;> rfl

def epModify (ep : EpId) (epiId : EpiId) (event : EpollEvent) : FS.M Int := do
  let pt : PollTable := {}   -- init_poll_funcptr(&pt, NULL)
  let epi ← getEpi epiId
  setEpi epiId { epi with events := event.events, data := event.data }
  if ← branchCmp .epModifyWakeup (hasFlag event.events EPOLLWAKEUP) (event.events &&& EPOLLWAKEUP).toNat 0 then
    if ← branch .epModifyNoWakeupSource true then   -- !ep_has_wakeup_source(epi): ws is NULL
      unsupported "ep_create_wakeup_source: EPOLLWAKEUP survived ep_take_care_of_epollwakeup"
  else if ← branch .epModifyHasWakeupSource false then
    unsupported "ep_destroy_wakeup_source with a wakeup source"
  -- smp_mb()
  let revents ← epItemPollAt epiId pt 1
  let mut pwake := 0
  if ← branchCmp .epModifyReady (revents != 0) revents.toNat 0 then
    -- spin_lock_irq(&ep->lock)
    let epi ← getEpi epiId
    if ← branch .epModifyNotLinked (!epi.linked) then
      let e ← getEp ep
      setEp ep { e with rdllist := e.rdllist ++ [epiId] }
      setEpi epiId { epi with linked := true }
      if ← branch .epModifyWqActive (← waitqueueActive (.epWq ep)) then
        unsupported "wake_up(&ep->wq) at ep_modify: a task sleeping in epoll_wait (tier 2)"
      if ← branch .epModifyPollWaitActive (← waitqueueActive (.epPollWait ep)) then pwake := pwake + 1
    -- spin_unlock_irq(&ep->lock)
  if ← branch .epModifyPwake (pwake != 0) then epPollSafewake ep none 0
  return 0

theorem epModify_source (ep : EpId) (epiId : EpiId) (event : EpollEvent) :
    Leanux.epModify ep epiId event = epModify ep epiId event := by
  unfold Leanux.epModify epModify
  simp only [epItemPollAt_source] <;> rfl

def doEpollCtlBodyWith (insert : EpId → EpollEvent → FileId → Int → Bool → FS.M Int)
    (update : EpId → EpiId → EpollEvent → FS.M Int) (fId tId : FileId) (op : Int) (fd : Int) (events : UInt32) (data : UInt64) :
    FS.M (Int × Bool) := do
  let fFile ← getFile fId
  let tFile ← getFile tId
  -- `!file_can_poll(fd_file(tf))`: `f_op->poll` NULL (modelled, unexercised: design 9.3)
  if ← branch .doEpollCtlCannotPoll (!(← fopsOf tFile.fOp).poll) then return (-EPERM, false)
  let mut events := events
  -- ep_op_has_event(op): `op != EPOLL_CTL_DEL`; ep_take_care_of_epollwakeup without CONFIG_PM_SLEEP
  if ← branchCmp .doEpollCtlHasEvent (op != EPOLL_CTL_DEL) op EPOLL_CTL_DEL then events := events &&& ~~~EPOLLWAKEUP
  -- error = -EINVAL; `fd_file(f) == fd_file(tf) || !is_file_epoll(fd_file(f))`
  let bad ← do
    if ← branch .doEpollCtlSameFile (fId == tId) then pure true
    else branch .doEpollCtlNotEpoll (!isFileEpoll fFile)
  if bad then return (-EINVAL, false)
  -- EPOLLEXCLUSIVE at ADD time only, never on an epoll target, only its OK bits
  let exclusiveBad ← do
    if ← branch .doEpollCtlExclusiveHasEvent (op != EPOLL_CTL_DEL) then
      if ← branchCmp .doEpollCtlExclusive (hasFlag events EPOLLEXCLUSIVE) (events &&& EPOLLEXCLUSIVE).toNat 0 then
        if ← branchCmp .doEpollCtlExclusiveMod (op == EPOLL_CTL_MOD) op EPOLL_CTL_MOD then pure true
        else if ← branchCmp .doEpollCtlExclusiveAdd (op == EPOLL_CTL_ADD) op EPOLL_CTL_ADD then
          if ← branch .doEpollCtlExclusiveTargetEpoll (isFileEpoll tFile) then pure true
          else branchCmp .doEpollCtlExclusiveBadBits (events &&& ~~~EPOLLEXCLUSIVE_OK_BITS != 0)
                 (events &&& ~~~EPOLLEXCLUSIVE_OK_BITS).toNat 0
        else pure false
      else pure false
    else pure false
  if exclusiveBad then return (-EINVAL, false)
  let ep ← epOf fFile
  let error ← epollMutexLock false   -- epoll_mutex_lock(&ep->mtx, 0, nonblock)
  if ← branch .doEpollCtlLockError (error != 0) then return (error, false)
  let mut fullCheck := false
  let mut tep : Option EpId := none
  if ← branch .doEpollCtlIsAdd (op == EPOLL_CTL_ADD) then   -- folded after the exclusive block
    let e ← getEp ep
    -- `f->f_ep || ep->gen == loop_check_gen || is_file_epoll(tf)`
    let nested ← do
      if ← branch .doEpollCtlEpfdWatched (fFile.fEp != .null) then pure true
      else if ← branchCmpExcluded .doEpollCtlGenMatches (e.gen == (← get).loopCheckGen) .loopCheckGen then
        invariant "a set's gen equal to loop_check_gen outside a check: the fixture's warm-up rule (design 3.5)"
      else branch .doEpollCtlTargetEpoll (isFileEpoll tFile)
    if nested then
      -- mutex_unlock(&ep->mtx); epoll_mutex_lock(&epnested_mutex, 0, nonblock)
      let error ← epollMutexLock false
      if ← branch .doEpollCtlNestedLockError (error != 0) then return (error, false)
      modify fun k => { k with loopCheckGen := k.loopCheckGen + 1 }
      fullCheck := true
      if ← branch .doEpollCtlTargetEpollLoop (isFileEpoll tFile) then
        tep := some (← epOf tFile)
        -- error = -ELOOP
        if ← branch .doEpollCtlEloop ((← epLoopCheck ep tep.get!) != 0) then return (-ELOOP, true)
      let error ← epollMutexLock false   -- epoll_mutex_lock(&ep->mtx, 0, nonblock)
      if ← branch .doEpollCtlRelockError (error != 0) then return (error, true)
  let epi ← epFind ep tId fd
  let mut error : Int := -EINVAL
  -- switch (op): one choice point in the C, lowered to one compare and a jump table;
  -- the three arms are plain decisions (no per-arm compare exists in the built code:
  -- the same-record rule of the mutation campaign showed all three matching one record)
  if ← branch .doEpollCtlCaseAdd (op == EPOLL_CTL_ADD) then
    if ← branch .doEpollCtlAddAbsent epi.isNone then
      events := events ||| EPOLLERR ||| EPOLLHUP
      error ← insert ep ⟨events, data⟩ tId fd fullCheck
    else error := -EEXIST
  else if ← branch .doEpollCtlCaseDel (op == EPOLL_CTL_DEL) then
    if ← branch .doEpollCtlDelPresent epi.isSome then
      epRemove ep epi.get!
      error := 0
    else error := -ENOENT
  else if ← branch .doEpollCtlCaseMod (op == EPOLL_CTL_MOD) then
    if ← branch .doEpollCtlModPresent epi.isSome then
      let item ← getEpi epi.get!
      if ← branchCmp .doEpollCtlModNotExclusive (!hasFlag item.events EPOLLEXCLUSIVE) (item.events &&& EPOLLEXCLUSIVE).toNat 0 then
        events := events ||| EPOLLERR ||| EPOLLHUP
        error ← update ep epi.get! ⟨events, data⟩
    else error := -ENOENT
  -- mutex_unlock(&ep->mtx)
  return (error, fullCheck)

theorem doEpollCtlBodyWith_source (fId tId : FileId) (op fd : Int) (events : UInt32) (data : UInt64) :
    (noise_const _private.Leanux.FS.Eventpoll.«0».Leanux.doEpollCtlBody) fId tId op fd events data =
      doEpollCtlBodyWith Leanux.epInsert Leanux.epModify fId tId op fd events data := rfl

def doEpollCtlBody (fId tId : FileId) (op fd : Int) (events : UInt32) (data : UInt64) : FS.M (Int × Bool) :=
  doEpollCtlBodyWith epInsert epModify fId tId op fd events data

theorem doEpollCtlBody_source (fId tId : FileId) (op fd : Int) (events : UInt32) (data : UInt64) :
    (noise_const _private.Leanux.FS.Eventpoll.«0».Leanux.doEpollCtlBody) fId tId op fd events data =
      doEpollCtlBody fId tId op fd events data := by
  rw [doEpollCtlBodyWith_source]
  have a : Leanux.epInsert = epInsert := funext fun ep => funext fun ev => funext fun fid => funext fun fd => funext (epInsert_source ep ev fid fd)
  have b : Leanux.epModify = epModify := funext fun ep => funext fun epi => funext (epModify_source ep epi)
  rw [a, b]
  rfl

def doEpollCtl (epfd : Nat) (op : Int) (fd : Int) (events : UInt32) (data : UInt64) : FS.M Int := do
  let f ← fdget epfd
  if ← branch .doEpollCtlEpfdEmpty f.file.isNone then
    fdput f
    return -EBADF
  let tf ← fdget (fd % 4294967296).toNat   -- `unsigned int fd`: the low 32 bits
  if ← branch .doEpollCtlFdEmpty tf.file.isNone then
    fdput tf
    fdput f
    return -EBADF
  let (error, fullCheck) ← doEpollCtlBody f.file.get! tf.file.get! op fd events data
  -- error_tgt_fput:
  if ← branch .doEpollCtlFullCheckExit fullCheck then   -- threaded away on the early exits
    clearTfileCheckList
    modify fun k => { k with loopCheckGen := k.loopCheckGen + 1 }
    -- mutex_unlock(&epnested_mutex)
  fdput tf
  fdput f
  return error

theorem doEpollCtl_source (epfd : Nat) (op fd : Int) (events : UInt32) (data : UInt64) :
    Leanux.doEpollCtl epfd op fd events data = doEpollCtl epfd op fd events data := by
  unfold Leanux.doEpollCtl doEpollCtl
  simp only [doEpollCtlBody_source] <;> rfl

def sysEpollCtl (epfd : Nat) (op : Int) (fd : Int) (events : UInt32) (data : UInt64) : FS.M Int := do
  if ← branchCmp .sysEpollCtlHasEvent (op != EPOLL_CTL_DEL) op EPOLL_CTL_DEL then
    if ← branch .sysEpollCtlCopyFault false then return -EFAULT
  doEpollCtl epfd op fd events data

theorem sysEpollCtl_source (epfd : Nat) (op fd : Int) (events : UInt32) (data : UInt64) :
    Leanux.sysEpollCtl epfd op fd events data = sysEpollCtl epfd op fd events data := by
  unfold Leanux.sysEpollCtl sysEpollCtl
  simp only [doEpollCtl_source] <;> rfl


end Leanux.Proofs.WG.Progress.FsFinite
