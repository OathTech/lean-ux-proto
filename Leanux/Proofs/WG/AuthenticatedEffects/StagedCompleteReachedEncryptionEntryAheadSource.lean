import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedEncryptionEntryCases

/-! A fixed split of the original crypt-ahead branch. The prefix retains
all hidden-record, queue-head and suspended-activation guards, and temporarily
requeues the TX peer before the nested encryption iteration. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionEntry
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open CompleteProduct

def aheadPrefix (pid : PeerId) : PrefixM CausalJournal.Event (Option Activation) := do
  if (← liftPrefix getAmbient).hidden.isNone then return none
  let some item := (← liftPrefix (liftWG (getPeer pid))).txQueue.all.head? | return none
  let some id := item.head? | liftPrefix (invariant "an empty ring item")
  if (← liftPrefix (liftWG (getTxSkb id))).state != .uncrypted then return none
  let next ← liftPrefix peekHiddenSite
  unless next == some HiddenSite.modTimerArm.info.id || next == some HiddenSite.timerJiffiesTraversal.info.id do return none
  let some enc := (← liftPrefix getAmbient).suspended.find? (·.worker == .encryptWorker)
    | liftPrefix (throw (.hidden "the tx worker's head is uncrypted and no encrypt activation is suspended, but the next record is the traversal timer's caller read or arm (site 426 or 100)"))
  liftPrefix (liftWG (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue ++ [pid]}))
  pure (some enc)

def aheadFinish (pid : PeerId) (enc : Activation) (result : IterResult) : PrefixM CausalJournal.Event Unit := do
  liftPrefix (liftWG (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue.erase pid}))
  match result with
  | .continued =>
    liftPrefix (modifyAmbient fun s => {s with suspended := s.suspended.map fun x =>
      if x == enc then {x with iterations := x.iterations + 1} else x})
  | .ended => liftPrefix (throw (.hidden "the encrypt activation's queue is empty, but the next record is the traversal timer's caller read or arm (site 426 or 100)"))
  | .yielded => liftPrefix (invariant "the encrypt activation yielded on a record that is not a resched")

def aheadBranch (pid : PeerId) : Option Activation → PrefixM CausalJournal.Event Unit
  | none => pure ()
  | some enc => Driver.encryptIterObserved CausalJournal.hooks >>= aheadFinish pid enc

theorem ahead_factor (pid : PeerId) :
    Driver.cryptAheadObserved CausalJournal.hooks pid = (aheadPrefix pid >>= aheadBranch pid) := by
  unfold Driver.cryptAheadObserved aheadPrefix
  simp only [bind_assoc]
  apply congrArg (fun next : Ambient → PrefixM CausalJournal.Event Unit => liftPrefix getAmbient >>= next)
  funext ambient
  by_cases hidden : ambient.hidden.isNone = true
  · simp only [hidden,↓reduceIte,pure_bind,aheadBranch]
  · simp only [hidden,Bool.false_eq_true,↓reduceIte,bind_assoc]
    apply congrArg (fun next : Peer → PrefixM CausalJournal.Event Unit =>
      liftPrefix (liftWG (getPeer pid)) >>= next)
    funext peer
    cases held : peer.txQueue.all.head? with
    | none => simp only [pure_bind,aheadBranch]
    | some item =>
      dsimp only
      cases first : item.head? with
      | none => rfl
      | some id =>
        simp only [bind_assoc]
        apply congrArg (fun next : DataPacket → PrefixM CausalJournal.Event Unit =>
          liftPrefix (liftWG (getTxSkb id)) >>= next)
        funext packet
        by_cases state : (packet.state != .uncrypted) = true
        · simp only [state,↓reduceIte,pure_bind,aheadBranch]
        · simp only [state,Bool.false_eq_true,↓reduceIte,bind_assoc]
          apply congrArg (fun next : Option Nat → PrefixM CausalJournal.Event Unit =>
            liftPrefix peekHiddenSite >>= next)
          funext site
          by_cases enabled : (site == some HiddenSite.modTimerArm.info.id ||
              site == some HiddenSite.timerJiffiesTraversal.info.id) = true
          · simp only [enabled,↓reduceIte,bind_assoc]
            apply congrArg (fun next : Ambient → PrefixM CausalJournal.Event Unit => liftPrefix getAmbient >>= next)
            funext saved
            cases selected : saved.suspended.find? (·.worker == .encryptWorker) with
            | none => rfl
            | some enc =>
              simp only [bind_assoc,pure_bind,aheadBranch]
              rfl
          · simp only [enabled,Bool.false_eq_true,↓reduceIte,pure_bind,aheadBranch]

theorem ahead_prefix_checked (pid : PeerId) : Checked (aheadPrefix pid) := by
  unfold aheadPrefix
  repeat' first
    | solve | complete_scheduler_native
    | complete_product_step

theorem ahead_finish_checked (pid : PeerId) (enc : Activation) (result : IterResult) :
    Checked (aheadFinish pid enc result) := by
  unfold aheadFinish
  apply bind_checked (wg _ (erase_work pid))
  intro ignored
  cases result with
  | continued => exact ambient _
  | ended => exact throw_checked _
  | yielded => exact ambient _

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionEntry
