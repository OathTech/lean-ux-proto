import Leanux.Proofs.WG.TimerDiscipline.SectionFrames
import Leanux.Proofs.WG.TimerDiscipline.FireUnitSource
import Leanux.Proofs.WG.TimerDiscipline.RetrySource

/-! Current selected wheel-unit contracts. The outer nextDue branch and complete runTimers loop are separate obligations. -/

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Env Noise Std.Do

theorem detach_retransmit (pid : PeerId) (identity attempts : Nat) (timer : Option UInt64) :
    ⦃fun g => ⌜retryAt g pid = some (identity, attempts, timer)⌝⦄ delTimer pid .retransmitHandshake
      ⦃⇓? _ g => ⌜retryAt g pid = some (identity, attempts, none)⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  unfold delTimer
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_spec pid _)) ?_
  intro p g ambient result final after pre run
  have value : retryView p = (identity, attempts, timer) := by
    simpa [retryAt, pre.2] using pre.1
  cases run
  cases device : g.dev with
  | none => simp [peerAt, device] at pre
  | some d =>
    simp only [retryView, Prod.mk.injEq] at value
    simp [retryAt, peerAt, device, Peer.setTimer, Peer.setWheel, retryView, value.1, value.2.1]

/-- Current selected wheel-unit callback. Detachment clears expiry and wheel membership; pass-step writes preserve the retry observation. -/
theorem fireSelected_retransmit (pid : PeerId) (we : WheelEntry)
    (identity attempts : Nat) (timer : Option UInt64) :
    Noise.Product.Ensures (fireWheelSelected .timerRetransmit pid .retransmitHandshake we)
      (fun w => retryAt w.wg pid = some (identity, attempts, timer))
      (fun _ w => retryAt w.wg pid = some (identity, nextAttempts attempts, none)) := by
  have lifted {α : Type} (action : WG.M α) (P : WGWorld → Prop) (Q : α → WGWorld → Prop)
      (contract : Noise.Ensures action P Q) :
      Noise.Product.Ensures (liftWG action) (fun w => P w.wg) (fun value w => Q value w.wg) := by
    intro entry value final pre run
    change ((action.run entry.wg).run entry.ambient >>= _) = _ at run
    cases actual : (action.run entry.wg).run entry.ambient with
    | error stop => rw [actual] at run; cases run
    | ok pair =>
      obtain ⟨⟨result, current⟩, inputs⟩ := pair
      rw [actual] at run
      cases run
      exact contract entry.wg entry.ambient value current inputs pre actual
  have detached := lifted _ _ _ ((ensures_iff _ _ _).mpr (detach_retransmit pid identity attempts timer))
  have callback := lifted _ _ _ (expiredRetransmit_retryView pid identity attempts none)
  have sectionContract := (Noise.Product.ensures_iff _ _ _).mpr
    (runTimerSection_kernel_contract .timerRetransmit (liftWG (expiredRetransmitHandshake pid))
      (fun g _ _ _ => retryAt g pid = some (identity, attempts, none))
      (fun g _ _ _ => retryAt g pid = some (identity, nextAttempts attempts, none))
      ((Noise.Product.ensures_iff _ _ _).mp callback))
  change Noise.Product.Ensures (do
    liftWG (delTimer pid .retransmitHandshake)
    modifyWG fun s => {s with timerPassStep := some we.bucketExpiry}
    runTimerSection .timerRetransmit (liftWG (expiredRetransmitHandshake pid))
    modifyWG fun s => {s with timerPassStep := none}) _ _
  refine Noise.Product.ensures_bind _ _ detached ?_
  intro ignored
  refine Noise.Product.ensures_bind (Q := fun _ w => retryAt w.wg pid = some (identity, attempts, none)) _ _ ?_ ?_
  · intro entry value final pre run
    cases run
    exact pre
  · intro ignored
    refine Noise.Product.ensures_bind _ _ sectionContract ?_
    intro ignored entry value final pre run
    cases run
    exact pre

end Leanux.Proofs.WG.TimerDiscipline
