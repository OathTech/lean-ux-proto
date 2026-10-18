import Leanux.Proofs.WG.AuthenticatedEffects.WorkRootSource
import Leanux.Proofs.WG.Queues.RxConsumeProtection

/-! Native erasure and callback-history frames for deferred-work creation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.WorkRoot
open Leanux Leanux.WG Leanux.Proofs.Logged Origins.HandshakeSources TimerRoot Queues.RxCredits
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

private theorem lift_erases (a : WG.M α) : ErasesStatePrefix (liftWGPrefix a : WGPrefix Event α) a :=
  erasesStatePrefix_lift a
private theorem lift_frame (a : WG.M α) : StateHistoryFrame base (liftWGPrefix a) := by intro w a h; rfl
private theorem pure_frame (x : α) : StateHistoryFrame base (pure x : WGPrefix Event α) := by intro w a h; rfl
private theorem frame_choice (p : Prop) [Decidable p] (a b : WGPrefix Event α)
    (ha : StateHistoryFrame base a) (hb : StateHistoryFrame base b) :
    StateHistoryFrame base (if p then a else b) := by split <;> assumption
private theorem frame_loop (xs : List α) (initial : β) (g : α → β → WGPrefix Event (ForInStep β))
    (hg : ∀ x state, StateHistoryFrame base (g x state)) :
    StateHistoryFrame base (forIn xs initial g) := by
  induction xs generalizing initial with
  | nil => simpa only [List.forIn_nil] using pure_frame initial
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply StateHistoryFrame.bind (hg x initial)
    intro step
    cases step with
    | done state => exact pure_frame state
    | yield state => exact ih state

theorem enqueue_erases (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) :
    ErasesStatePrefix (enqueue origin kind pid)
      (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}) :=
  receiptWGObserved_erases (lift_erases _) _
theorem submit_erases (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) (items : List SkbId) :
    ErasesStatePrefix (submit origin kind pid items) (createData pid items) :=
  receiptWGObserved_erases (lift_erases _) _
theorem enqueue_frame (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) :
    StateHistoryFrame base (enqueue origin kind pid) :=
  StateHistoryFrame.receiptWGObserved (lift_frame _) _ (fun _ => rfl)
theorem submit_frame (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) (items : List SkbId) :
    StateHistoryFrame base (submit origin kind pid items) :=
  StateHistoryFrame.receiptWGObserved (lift_frame _) _ (fun _ => rfl)

macro "work_root_erasure_step" : tactic => `(tactic| first
  | with_reducible exact lift_erases _
  | with_reducible exact erasesStatePrefix_pure _
  | with_reducible apply erasesStatePrefix_forIn
  | with_reducible apply erasesStatePrefix_bind
  | contradiction
  | split
  | causal_erases_choice
  | (session_origin_intro_forall; try dsimp only)
  | simp +failIfUnchanged only [bind_assoc,pure_bind])

elab "work_root_frame_choice" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.isAppOf ``StateHistoryFrame do Lean.throwError "expected history frame"
  unless target.getAppArgs.back!.isAppOf ``ite do Lean.throwError "expected choice"
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply frame_choice))

macro "work_root_frame_step" : tactic => `(tactic| first
  | with_reducible exact lift_frame _
  | with_reducible exact pure_frame _
  | with_reducible apply frame_loop
  | with_reducible apply StateHistoryFrame.bind
  | contradiction
  | split
  | work_root_frame_choice
  | (session_origin_intro_forall; try dsimp only)
  | simp +failIfUnchanged only [bind_assoc,pure_bind])

theorem queued_erases (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) (retry : Bool) :
    ErasesStatePrefix (queued origin kind pid retry) (sendQueuedHandshakeInitiation pid retry) := by
  unfold queued sendQueuedHandshakeInitiation
  repeat' first | with_reducible exact enqueue_erases _ _ _ | work_root_erasure_step

theorem queued_frame (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) (retry : Bool) :
    StateHistoryFrame base (queued origin kind pid retry) := by
  unfold queued
  repeat' first | with_reducible exact enqueue_frame _ _ _ | work_root_frame_step

theorem noKey_erases (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) (packets : List WG.Packet)
    (kp : Option KeypairId) (invalid : Bool) :
    ErasesStatePrefix (noKey origin kind pid packets kp invalid) (Lifetimes.stagedOutNokey pid packets kp invalid) := by
  unfold noKey Lifetimes.stagedOutNokey
  cases invalid <;> cases kp <;> simp only [Bool.false_eq_true,↓reduceIte]
  all_goals repeat' first | with_reducible exact queued_erases _ _ _ _ | work_root_erasure_step

theorem noKey_frame (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) (packets : List WG.Packet)
    (kp : Option KeypairId) (invalid : Bool) : StateHistoryFrame base (noKey origin kind pid packets kp invalid) := by
  unfold noKey
  cases invalid <;> cases kp <;> simp only [Bool.false_eq_true,↓reduceIte]
  all_goals repeat' first | with_reducible exact queued_frame _ _ _ _ | work_root_frame_step

theorem key_erases (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) (id : KeypairId) (packets : List WG.Packet) :
    ErasesStatePrefix (key origin kind pid id packets) (stagedKeySource pid id packets) := by
  unfold key stagedKeySource stagedSubmit Affiliation.sendAcquire
  repeat' first
    | with_reducible exact noKey_erases _ _ _ _ _ _
    | with_reducible exact submit_erases _ _ _ _
    | work_root_erasure_step

theorem key_frame (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) (id : KeypairId) (packets : List WG.Packet) :
    StateHistoryFrame base (key origin kind pid id packets) := by
  unfold key
  repeat' first
    | with_reducible exact noKey_frame _ _ _ _ _ _
    | with_reducible exact submit_frame _ _ _ _
    | work_root_frame_step

theorem staging_erases (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) :
    ErasesStatePrefix (staging origin kind pid) (sendStagedPackets pid) := by
  rw [← stagedFullSource_eq]
  unfold staging stagedFullSource
  repeat' first
    | with_reducible exact noKey_erases _ _ _ _ _ _
    | with_reducible exact key_erases _ _ _ _ _
    | work_root_erasure_step
  all_goals simp_all only [Option.some.injEq]
  all_goals first | with_reducible exact key_erases _ _ _ _ _ | simp_all

theorem staging_frame (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) :
    StateHistoryFrame base (staging origin kind pid) := by
  unfold staging
  repeat' first
    | with_reducible exact noKey_frame _ _ _ _ _ _
    | with_reducible exact key_frame _ _ _ _ _
    | work_root_frame_step

theorem keepalive_erases (origin : Nat) (pid : PeerId) :
    ErasesStatePrefix (keepalive origin pid) (sendKeepalive pid) := by
  unfold keepalive sendKeepalive
  repeat' first | with_reducible exact staging_erases _ _ _ | work_root_erasure_step

theorem keepalive_frame (origin : Nat) (pid : PeerId) : StateHistoryFrame base (keepalive origin pid) := by
  unfold keepalive
  repeat' first | with_reducible exact staging_frame _ _ _ | work_root_frame_step

end Leanux.Proofs.WG.AuthenticatedEffects.WorkRoot
