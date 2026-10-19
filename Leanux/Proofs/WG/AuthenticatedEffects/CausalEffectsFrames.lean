import Leanux.Proofs.WG.AuthenticatedEffects.PacketEffectsFrames

/-! Effect receipts preserve the scope stack. Consequently the next effect in
the same dynamic callback reads the same context until an explicit scope event. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalEffects
open Leanux Leanux.WG Leanux.Proofs.Logged

theorem atCurrent_frame (decode : E → Option (CausalScope.Event Cause))
    (body : Context Cause → WGPrefix E α) (ρ : E → Option F)
    (frame : ∀ context, StateHistoryFrame ρ (body context)) :
    StateHistoryFrame ρ (atCurrent decode body) :=
  fun w a h => frame (CausalScope.current decode h) w a h

theorem ops_frames (decode : E → Option (CausalScope.Event Cause))
    (recordArm : TimerEffects.Arm (Context Cause) → E)
    (recordQueue : TimerEffects.Queued (Context Cause) → E)
    (ρ : E → Option F) (ha : ∀ r, ρ (recordArm r) = none) (hq : ∀ r, ρ (recordQueue r) = none) :
    TimerEffects.Ops.Frames ρ (ops decode recordArm recordQueue) where
  step := by intro α action w a h; rfl
  arm := fun pid timer delay caller => atCurrent_frame decode _ ρ (fun context =>
    StateHistoryFrame.receiptWGObserved (by intro w a h; rfl) _ (fun _ => ha _))
  append := fun pid => atCurrent_frame decode _ ρ (fun context =>
    StateHistoryFrame.receiptWGObserved (by intro w a h; rfl) _ (fun _ => hq _))

end Leanux.Proofs.WG.AuthenticatedEffects.CausalEffects
