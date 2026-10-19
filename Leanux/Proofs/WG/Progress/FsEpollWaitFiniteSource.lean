import Leanux.Proofs.WG.Progress.FsEpollPollFiniteSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.FsFinite
open Leanux

/-! Finite epoll delivery and wait callers using the existing finite
poll factor. Native timeout/sleep refusals and captured scans remain exact. -/

def epDeliverEvent (ep : EpId) (epiId : EpiId) (pt : PollTable) : FS.M (Int × ByteArray) := do
  -- list_del_init(&epi->rdllink): the item leaves the scan batch
  setEpi epiId { (← getEpi epiId) with linked := false }
  let revents ← epItemPollAt epiId pt 1
  if ← branchCmp .epDeliverEventNotReady (revents == 0) revents.toNat 0 then return (0, ByteArray.empty)
  let epi ← getEpi epiId
  let next ← epollPutUevent revents epi.data
  if ← branch .epDeliverEventPutFault next.isNone then
    unsupported "copy_to_user faulted in epoll_put_uevent (the guest's buffer is valid)"
  let bytes := next.get!
  if ← branchCmp .epDeliverEventOneshot (hasFlag epi.events EPOLLONESHOT) (epi.events &&& EPOLLONESHOT).toNat 0 then
    setEpi epiId { epi with events := epi.events &&& EP_PRIVATE_BITS }
  -- `!(events & EPOLLET)`: bit 31, the sign test `(int)events >= 0` in the built code
  else if ← branchCmp .epDeliverEventLevelTriggered (!hasFlag epi.events EPOLLET) epi.events.toNat 0 then
    -- list_add_tail(&epi->rdllink, &ep->rdllist); ep_pm_stay_awake (empty)
    let e ← getEp ep
    setEp ep { e with rdllist := e.rdllist ++ [epiId] }
    setEpi epiId { (← getEpi epiId) with linked := true }
  return (1, bytes)

theorem epDeliverEvent_source (ep : EpId) (epiId : EpiId) (pt : PollTable) :
    Leanux.epDeliverEvent ep epiId pt = epDeliverEvent ep epiId pt := by
  unfold Leanux.epDeliverEvent epDeliverEvent
  simp only [epItemPollAt_source] <;> rfl

def epSendEvents (ep : EpId) (maxevents : Int) : FS.M (Int × ByteArray) := do
  if ← branch .epSendEventsFatalSignal false then return (-EINTR, ByteArray.empty)   -- no signal pending (design 5)
  let pt : PollTable := {}   -- init_poll_funcptr(&pt, NULL)
  -- mutex_lock(&ep->mtx)
  let batch ← epStartScan ep
  let mut res : Int := 0
  let mut out := ByteArray.empty
  let mut remaining := batch
  let mut broke := false
  for epiId in batch do
    _ ← branch .epSendEventsIter true
    if ← branch .epSendEventsFull (res >= maxevents) then   -- folded on the first iteration
      broke := true
      break
    let (delivered, bytes) ← epDeliverEvent ep epiId pt
    remaining := remaining.erase epiId
    if ← branch .epSendEventsDeliverError (delivered < 0) then
      if ← branch .epSendEventsFirstError (res == 0) then res := delivered
      broke := true
      break
    res := res + delivered
    out := out ++ bytes
  if !broke then _ ← branch .epSendEventsIter false
  epDoneScan ep remaining
  -- mutex_unlock(&ep->mtx)
  return (res, out)

theorem epSendEvents_source (ep : EpId) (maxevents : Int) :
    Leanux.epSendEvents ep maxevents = epSendEvents ep maxevents := by
  unfold Leanux.epSendEvents epSendEvents
  simp only [epDeliverEvent_source] <;> rfl

def epPoll (ep : EpId) (maxevents : Int) (timeout : Option Timespec64) : FS.M (Int × ByteArray) := do
  let mut timedOut := false
  -- `timeout && (timeout->tv_sec | timeout->tv_nsec)`
  let positive ← do
    if ← branch .epPollHasTimeout timeout.isSome then
      let t := timeout.get!
      -- `tv_sec | tv_nsec`: both non-negative here (ep_timeout_to_timespec)
      let orv : Int := t.tvSec.toNat ||| t.tvNsec.toNat
      branchCmp .epPollTimeoutNonzero (orv != 0) orv 0
    else pure false
  if positive then unsupported "a positive epoll_wait timeout: select_estimate_accuracy (tier 2)"
  else if ← branch .epPollTimeoutAgain timeout.isSome then timedOut := true
  let eavail ← epEventsAvailable ep
  -- while (1): the first iteration; a second needs a sleep or a busy loop
  let mut result : Option (Int × ByteArray) := none
  if ← branchCmp .epPollEavail eavail (if eavail then 1 else 0) 0 then
    let (res, out) ← epSendEvents ep maxevents
    if ← branch .epPollSent (res != 0) then result := some (res, out)   -- folded after the maxevents break
  if let some r := result then return r
  if ← branchCmp .epPollTimedOut timedOut (if timedOut then 1 else 0) 0 then return (0, ByteArray.empty)
  unsupported "epoll_wait would sleep: ep_busy_loop, signal_pending and the wait on ep->wq (tier 2)"

theorem epPoll_source (ep : EpId) (maxevents : Int) (timeout : Option Timespec64) :
    Leanux.epPoll ep maxevents timeout = epPoll ep maxevents timeout := by
  unfold Leanux.epPoll epPoll
  simp only [epSendEvents_source] <;> rfl

def doEpollWait (epfd : Nat) (maxevents : Int) (to : Option Timespec64) : FS.M Int := do
  -- one unsigned range check in the built code, `(unsigned)(maxevents - 1) >
  -- EP_MAX_EVENTS - 1`, its operands on the second decision
  let bad ← do
    if ← branch .doEpollWaitMaxeventsNonpositive (maxevents <= 0) then pure true
    else branchCmp .doEpollWaitMaxeventsTooMany (maxevents > EP_MAX_EVENTS)
           ((maxevents - 1) % 4294967296) (EP_MAX_EVENTS - 1)
  if bad then return -EINVAL
  -- access_ok(events, maxevents * sizeof(struct epoll_event)): the guest's buffer
  if ← branch .doEpollWaitAccessNotOk false then return -EFAULT
  let f ← fdget epfd
  if ← branch .doEpollWaitNoFile f.file.isNone then return -EBADF
  let fid := f.file.get!
  let mut error : Int := -EINVAL
  if ← branch .doEpollWaitNotEpoll (!isFileEpoll (← getFile fid)) then pure ()   -- goto error_fput
  else
    let ep ← epOf (← getFile fid)
    let (res, out) ← epPoll ep maxevents to
    error := res
    modify fun w => { w with userOut := some out }
  fdput f   -- error_fput:
  return error

theorem doEpollWait_source (epfd : Nat) (maxevents : Int) (to : Option Timespec64) :
    Leanux.doEpollWait epfd maxevents to = doEpollWait epfd maxevents to := by
  unfold Leanux.doEpollWait doEpollWait
  simp only [epPoll_source] <;> rfl

def sysEpollWait (epfd : Nat) (maxevents timeout : Int) : FS.M Int := do
  let to ← epTimeoutToTimespec timeout
  doEpollWait epfd maxevents to

theorem sysEpollWait_source (epfd : Nat) (maxevents timeout : Int) :
    Leanux.sysEpollWait epfd maxevents timeout = sysEpollWait epfd maxevents timeout := by
  unfold Leanux.sysEpollWait sysEpollWait
  simp only [doEpollWait_source] <;> rfl


end Leanux.Proofs.WG.Progress.FsFinite
