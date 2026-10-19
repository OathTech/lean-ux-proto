import Leanux.Proofs.WG.Progress.FsPollFiniteSource
import Leanux.FS.Eventpoll

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.FsFinite
open Leanux

/-! One callback seam for the actual mutually recursive, fuel-bounded
poll source. Both native nesting budgets and exhaustion Stops are retained. -/

mutual

def epItemPollWith (poll : FileId → PollTable → FS.M UInt32)
    (register : FileId → WaitQueueRef → PollTable → FS.M Unit) (fuel : Nat) (epiId : EpiId) (pt : PollTable) (depth : Nat) : FS.M UInt32 := do
  let epi ← getEpi epiId
  -- file = epi_fget(epi)
  let got ← fileIncNotZero epi.file
  _ ← branch .epiFgetIncNotZeroFailed (!got)
  if ← branch .epItemPollNoFile (!got) then
    invariant "epi_fget failed at ep_item_poll: the item's file has no reference"
  let pt := { pt with key := epi.events }   -- pt->_key = epi->event.events
  let file ← getFile epi.file
  let res ← if ← branch .epItemPollNotEpoll (!isFileEpoll file) then poll epi.file pt
            else match fuel with
              | 0 => invariant "ep_item_poll nested beyond EP_MAX_NESTS + 2"
              | fuel + 1 => epEventpollPollInnerWith poll register fuel epi.file pt depth
  fput epi.file
  return res &&& epi.events
termination_by (fuel, 0)

def epEventpollPollInnerWith (poll : FileId → PollTable → FS.M UInt32)
    (register : FileId → WaitQueueRef → PollTable → FS.M Unit) (fuel : Nat) (fid : FileId) (wait : PollTable) (depth : Nat) : FS.M UInt32 := do
  let ep ← epOf (← getFile fid)
  let pt : PollTable := {}   -- init_poll_funcptr(&pt, NULL)
  register fid (.epPollWait ep) wait
  -- mutex_lock_nested(&ep->mtx, depth)
  let batch ← epStartScan ep
  let mut res : UInt32 := 0
  let mut remaining := batch
  let mut broke := false
  for epiId in batch do
    _ ← branch .epEventpollPollIter true
    let r ← epItemPollWith poll register fuel epiId pt (depth + 1)
    if ← branchCmp .epEventpollPollReady (r != 0) r.toNat 0 then
      res := EPOLLIN ||| EPOLLRDNORM
      broke := true
      break
    -- __pm_relax(ep_wakeup_source(epi)) (empty); list_del_init(&epi->rdllink)
    remaining := remaining.erase epiId
    setEpi epiId { (← getEpi epiId) with linked := false }
  if !broke then _ ← branch .epEventpollPollIter false
  epDoneScan ep remaining
  -- mutex_unlock(&ep->mtx)
  return res
termination_by (fuel, 1)

end

theorem epPollWith_original (fuel : Nat) :
    (∀ epi pt depth, Leanux.epItemPoll fuel epi pt depth =
      epItemPollWith Leanux.vfsPoll Leanux.pollWait fuel epi pt depth) ∧
    (∀ fid pt depth, Leanux.epEventpollPollInner fuel fid pt depth =
      epEventpollPollInnerWith Leanux.vfsPoll Leanux.pollWait fuel fid pt depth) := by
  induction fuel with
  | zero =>
    have item : ∀ epi pt depth, Leanux.epItemPoll 0 epi pt depth =
        epItemPollWith Leanux.vfsPoll Leanux.pollWait 0 epi pt depth := by
      intro epi pt depth
      unfold Leanux.epItemPoll epItemPollWith
      rfl
    refine ⟨item, ?_⟩
    intro fid pt depth
    unfold Leanux.epEventpollPollInner epEventpollPollInnerWith
    simp only [item] <;> rfl
  | succ fuel ih =>
    have item : ∀ epi pt depth, Leanux.epItemPoll (fuel+1) epi pt depth =
        epItemPollWith Leanux.vfsPoll Leanux.pollWait (fuel+1) epi pt depth := by
      intro epi pt depth
      unfold Leanux.epItemPoll epItemPollWith
      simp only [ih.2] <;> rfl
    refine ⟨item, ?_⟩
    intro fid pt depth
    unfold Leanux.epEventpollPollInner epEventpollPollInnerWith
    simp only [item] <;> rfl

def epItemPoll (fuel : Nat) (epi : EpiId) (pt : PollTable) (depth : Nat) : FS.M UInt32 :=
  epItemPollWith vfsPoll pollWait fuel epi pt depth

def epEventpollPollInner (fuel : Nat) (fid : FileId) (pt : PollTable) (depth : Nat) : FS.M UInt32 :=
  epEventpollPollInnerWith vfsPoll pollWait fuel fid pt depth

theorem epItemPoll_source (fuel : Nat) (epi : EpiId) (pt : PollTable) (depth : Nat) :
    Leanux.epItemPoll fuel epi pt depth = epItemPoll fuel epi pt depth := by
  have h := (epPollWith_original fuel).1 epi pt depth
  have a : Leanux.vfsPoll = vfsPoll := funext fun fid => funext (vfsPoll_source fid)
  have b : Leanux.pollWait = pollWait := funext fun fid => funext fun head => funext (pollWait_source fid head)
  rw [a, b] at h
  exact h

theorem epEventpollPollInner_source (fuel : Nat) (fid : FileId) (pt : PollTable) (depth : Nat) :
    Leanux.epEventpollPollInner fuel fid pt depth = epEventpollPollInner fuel fid pt depth := by
  have h := (epPollWith_original fuel).2 fid pt depth
  have a : Leanux.vfsPoll = vfsPoll := funext fun fid => funext (vfsPoll_source fid)
  have b : Leanux.pollWait = pollWait := funext fun fid => funext fun head => funext (pollWait_source fid head)
  rw [a, b] at h
  exact h

def epItemPollAt (epiId : EpiId) (pt : PollTable) (depth : Nat) : FS.M UInt32 :=
  epItemPoll (EP_MAX_NESTS + 2) epiId pt depth

theorem epItemPollAt_source (epi : EpiId) (pt : PollTable) (depth : Nat) :
    Leanux.epItemPollAt epi pt depth = epItemPollAt epi pt depth := by
  unfold Leanux.epItemPollAt epItemPollAt
  exact epItemPoll_source _ _ _ _

end Leanux.Proofs.WG.Progress.FsFinite
