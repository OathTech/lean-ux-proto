import Leanux.Proofs.WG.AuthenticatedEffects.WorkRootFrames

/-! Structural append laws for the actual queue/staging observer, with no
incoming-history safety or queue-carrier premise. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.WorkRoot
open Leanux Leanux.WG Leanux.Proofs.Logged TimerRoot
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

private theorem lift_appends (action : WG.M α) : StateAppends (liftWGPrefix action : WGPrefix Event α) :=
  fun _ _ _ => ⟨[],by simp only [List.append_nil]; rfl⟩

private theorem loop_appends (xs : List α) (initial : β) (body : α → β → WGPrefix Event (ForInStep β))
    (each : ∀ x state, StateAppends (body x state)) : StateAppends (forIn xs initial body) := by
  induction xs generalizing initial with
  | nil => simpa only [List.forIn_nil] using StateAppends.pure initial
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply StateAppends.bind (each x initial)
    intro step
    cases step with
    | done state => exact StateAppends.pure state
    | yield state => exact ih state
private theorem choose_appends (p : Prop) [Decidable p] (a b : WGPrefix Event α)
    (ha : StateAppends a) (hb : StateAppends b) : StateAppends (if p then a else b) := by
  split <;> assumption
elab "work_appends_choice" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.isAppOf ``StateAppends do Lean.throwError "expected append law"
  unless target.getAppArgs.back!.isAppOf ``ite do Lean.throwError "expected choice"
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply choose_appends))
macro "work_appends_step" : tactic => `(tactic| first
  | with_reducible exact lift_appends _
  | with_reducible exact StateAppends.pure _
  | with_reducible apply StateAppends.bind
  | with_reducible apply loop_appends
  | work_appends_choice
  | split
  | (session_origin_intro_forall; try dsimp only)
  | simp +failIfUnchanged only [bind_assoc,pure_bind])

theorem enqueue_appends (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) :
    StateAppends (enqueue origin kind pid) := StateAppends.receiptWGObserved (StateAppends.lift _) _
theorem submit_appends (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) (items : List SkbId) :
    StateAppends (submit origin kind pid items) := StateAppends.receiptWGObserved (StateAppends.lift _) _
theorem queued_appends (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) (retry : Bool) :
    StateAppends (queued origin kind pid retry) := by
  unfold queued
  repeat' first | with_reducible exact enqueue_appends _ _ _ | work_appends_step

theorem noKey_appends (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) (packets : List Packet)
    (kp : Option KeypairId) (invalid : Bool) : StateAppends (noKey origin kind pid packets kp invalid) := by
  unfold noKey
  repeat' first | with_reducible exact queued_appends _ _ _ _ | work_appends_step

theorem key_appends (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) (id : KeypairId)
    (packets : List Packet) : StateAppends (key origin kind pid id packets) := by
  unfold key
  repeat' first
    | with_reducible exact noKey_appends _ _ _ _ _ _
    | with_reducible exact submit_appends _ _ _ _
    | work_appends_step

theorem staging_appends (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) :
    StateAppends (staging origin kind pid) := by
  unfold staging
  repeat' first
    | with_reducible exact noKey_appends _ _ _ _ _ _
    | with_reducible exact key_appends _ _ _ _ _
    | work_appends_step

theorem keepalive_appends (origin : Nat) (pid : PeerId) : StateAppends (keepalive origin pid) := by
  unfold keepalive
  repeat' first | with_reducible exact staging_appends _ _ _ | work_appends_step

end Leanux.Proofs.WG.AuthenticatedEffects.WorkRoot
