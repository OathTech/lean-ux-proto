import Leanux.Proofs.WG.Noise.PendingPollCompleteSource
import Leanux.Proofs.WG.Noise.PendingControlSource
import Leanux.Proofs.WG.Noise.PendingDispatchSource
import Leanux.Proofs.WG.Noise.PendingReceptionSource
import Leanux.Proofs.WG.Queues.SchedulerPreservation
import Leanux.Proofs.WG.Queues.DeferredPreservation

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingScheduler
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues PendingSession

theorem product_store {α : Type} (a : Leanux.M α) (frame : SameProductStore a) (seen : List Nat) :
    Preserves (fun w : World => NativeInv w.wg seen) a := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi run
  exact PendingSession.native_store w.wg v.wg seen
    (congrArg (fun s : ProductStore43 => s.2.2.2)
      ((ProjectedAction.iff_run _ _ _).mp frame w x v run)) hi

/- Native guard frames: these read the product store but never mutate it. -/
theorem requireDrained_store (what : String) (queues : List Bool) :
    SameProductStore (Env.requireDrained what queues) :=
  requireDrained_sameKernel what queues

theorem requireIdleDevice_store : SameProductStore Env.requireIdleDevice := by
  intro initial
  unfold Env.requireIdleDevice
  apply preserves_bind (requireNoCryptWork_sameKernel initial)
  intro _
  apply preserves_bind (productGetDev_spec (fun s => s = initial))
  intro d
  split
  · exact productAmbient_spec _ _ (fun _ _ hi => hi)
  · exact preserves_pure _

theorem requireStepComplete_store (bucket : UInt64) :
    SameProductStore (Env.requireStepComplete bucket) := by
  intro initial
  unfold Env.requireStepComplete
  apply preserves_bind (productGetDev_spec (fun s => s = initial))
  intro d
  cases TimerWheel.anotherAtStep d bucket with
  | none => exact preserves_pure _
  | some pair => rcases pair with ⟨pid,timer⟩; exact hoare_throw _

theorem sectionAppearsLater_store (worker : Worker) (unit : Nat) :
    SameProductStore (Env.sectionAppearsLater worker unit) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w x v run
  cases run
  rfl

theorem requireNothingDue_store (j : UInt64) :
    SameProductStore (Env.requireNothingDue j) := by
  intro initial
  unfold Env.requireNothingDue
  apply preserves_bind (productGetWG_spec (fun s => s = initial))
  intro w
  cases hd : w.dev with
  | none => simpa only [hd] using (preserves_pure () : Preserves (fun w : World => productStoreView w = initial) (pure () : Leanux.M Unit))
  | some d =>
    simp only
    cases hdue : TimerWheel.nextDue d j with
    | none => simpa only [hdue] using (preserves_pure () : Preserves (fun w : World => productStoreView w = initial) (pure () : Leanux.M Unit))
    | some due =>
      rcases due with ⟨pid,timer,entry⟩
      simp only
      apply preserves_bind (timerWorker_sameKernel timer initial)
      intro worker
      apply preserves_bind (productGetWG_spec (fun s => s = initial))
      intro next
      apply preserves_bind (sectionAppearsLater_store worker _ initial)
      intro later
      split
      · apply preserves_bind (productAmbient_spec _ _ (fun _ _ hi => hi))
        intro _
        exact hoare_throw _
      · exact hoare_throw _


end Leanux.Proofs.WG.Noise.PendingScheduler
