import Leanux.Proofs.WG.AuthenticatedEffects.WorkRootAppends
import Leanux.Proofs.WG.AuthenticatedEffects.TimerRootFacts
import Leanux.Proofs.WG.Queues.RxConsumeProtection

/-! Native keepalive and staging add no timer-arm receipt. This is an exact
history projection, including effects preceding a later Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.WorkRoot
open Leanux Leanux.WG Leanux.Proofs.Logged Origins.HandshakeSources TimerRoot Queues.RxCredits
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

private theorem lift_arms_frame (a : WG.M α) : StateHistoryFrame arms (liftWGPrefix a) := by intro w a h; rfl
private theorem pure_arms_frame (x : α) : StateHistoryFrame arms (pure x : WGPrefix Event α) := by intro w a h; rfl
private theorem arms_frame_choice (p : Prop) [Decidable p] (a b : WGPrefix Event α)
    (ha : StateHistoryFrame arms a) (hb : StateHistoryFrame arms b) :
    StateHistoryFrame arms (if p then a else b) := by split <;> assumption
private theorem arms_frame_loop (xs : List α) (initial : β) (g : α → β → WGPrefix Event (ForInStep β))
    (hg : ∀ x state, StateHistoryFrame arms (g x state)) :
    StateHistoryFrame arms (forIn xs initial g) := by
  induction xs generalizing initial with
  | nil => simpa only [List.forIn_nil] using pure_arms_frame initial
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply StateHistoryFrame.bind (hg x initial)
    intro step
    cases step with
    | done state => exact pure_arms_frame state
    | yield state => exact ih state

theorem enqueue_arms_frame (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) :
    StateHistoryFrame arms (enqueue origin kind pid) :=
  StateHistoryFrame.receiptWGObserved (lift_arms_frame _) _ (fun _ => rfl)
theorem submit_arms_frame (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) (items : List SkbId) :
    StateHistoryFrame arms (submit origin kind pid items) :=
  StateHistoryFrame.receiptWGObserved (lift_arms_frame _) _ (fun _ => rfl)

elab "work_root_arms_arms_frame_choice" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.isAppOf ``StateHistoryFrame do Lean.throwError "expected history frame"
  unless target.getAppArgs.back!.isAppOf ``ite do Lean.throwError "expected choice"
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply arms_frame_choice))

macro "work_root_arms_frame_step" : tactic => `(tactic| first
  | with_reducible exact lift_arms_frame _
  | with_reducible exact pure_arms_frame _
  | with_reducible apply arms_frame_loop
  | with_reducible apply StateHistoryFrame.bind
  | contradiction
  | split
  | work_root_arms_arms_frame_choice
  | (session_origin_intro_forall; try dsimp only)
  | simp +failIfUnchanged only [bind_assoc,pure_bind])

theorem queued_arms_frame (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) (retry : Bool) :
    StateHistoryFrame arms (queued origin kind pid retry) := by
  unfold queued
  repeat' first | with_reducible exact enqueue_arms_frame _ _ _ | work_root_arms_frame_step

theorem noKey_arms_frame (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) (packets : List WG.Packet)
    (kp : Option KeypairId) (invalid : Bool) : StateHistoryFrame arms (noKey origin kind pid packets kp invalid) := by
  unfold noKey
  cases invalid <;> cases kp <;> simp only [Bool.false_eq_true,↓reduceIte]
  all_goals repeat' first | with_reducible exact queued_arms_frame _ _ _ _ | work_root_arms_frame_step

theorem key_arms_frame (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) (id : KeypairId) (packets : List WG.Packet) :
    StateHistoryFrame arms (key origin kind pid id packets) := by
  unfold key
  repeat' first
    | with_reducible exact noKey_arms_frame _ _ _ _ _ _
    | with_reducible exact submit_arms_frame _ _ _ _
    | work_root_arms_frame_step

theorem staging_arms_frame (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) :
    StateHistoryFrame arms (staging origin kind pid) := by
  unfold staging
  repeat' first
    | with_reducible exact noKey_arms_frame _ _ _ _ _ _
    | with_reducible exact key_arms_frame _ _ _ _ _
    | work_root_arms_frame_step

theorem keepalive_arms_frame (origin : Nat) (pid : PeerId) : StateHistoryFrame arms (keepalive origin pid) := by
  unfold keepalive
  repeat' first | with_reducible exact staging_arms_frame _ _ _ | work_root_arms_frame_step

end Leanux.Proofs.WG.AuthenticatedEffects.WorkRoot
