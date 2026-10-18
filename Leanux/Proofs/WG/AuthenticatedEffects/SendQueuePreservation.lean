import Leanux.Proofs.WG.AuthenticatedEffects.SendQueueDataFrames

/-! The original native queueing source constructs the explicit occurrence
carrier. Its partial operations retain their original Stops. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.SendWorkCauses
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes TimerRoot Std.Do

abbrev Inventory (h : List Event) (w : WGWorld) (_ : Ambient) := ∃ tickets, Carrier h tickets w
abbrev Preserves (g : WGPrefix Event α) := StatePrefixPreserves Inventory (fun _ => True) g

theorem enqueue_preserves (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) :
    Preserves (WorkRoot.enqueue origin kind pid) := by
  intro w ambient h hi
  obtain ⟨tickets,carrier⟩ := hi
  have observed := runWGPrefix_receiptWGObserved
    (liftWGPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}))
    (fun r => Event.queued ⟨origin,kind,pid,r⟩) w ambient h
  simp only [runWGPrefix_lift] at observed
  change runWGPrefix (WorkRoot.enqueue origin kind pid) w ambient h = _ at observed
  simp only [runWGPrefix,runStatePrefix] at observed
  rw [observed]
  cases run : ((modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}).run w).run ambient with
  | error err => exact ⟨[],by simp,True.intro,True.intro⟩
  | ok out =>
    rcases out with ⟨⟨result,v⟩,b⟩
    cases result
    let receipt : Queued := ⟨origin,kind,pid,⟨(),w,v,ambient,b⟩⟩
    refine ⟨[.queued receipt],rfl,True.intro,?_⟩
    cases device : w.dev with
    | some d => exact ⟨tickets ++ [⟨h.length,receipt⟩],carrier.enqueue receipt run (by change w.dev.isSome; simp [device])⟩
    | none =>
      have queued := WorkRoot.queued_native_append receipt run
      have same : queue v = queue w := by
        change v.dev = w.dev.map _ at queued
        simp only [queue,queued,device,Option.map_none]
      exact ⟨tickets,(carrier.frame same).append [.queued receipt]⟩

theorem lift_preserves {action : WG.M α} (frame : SameView queue action) : Preserves (liftWGPrefix action) :=
  StatePrefixEnsures.lift action (fun _ _ _ _ => True.intro)
    (fun _ w a result v b hi run => by
      obtain ⟨tickets,carrier⟩ := hi
      exact ⟨tickets,carrier.frame ((ProjectedAction.iff_run_ambient _ _ _).mp frame w a result v b run)⟩)

theorem framed_receipt_preserves (action : WG.M α) (record : WGRunWitness α → Event)
    (frame : SameView queue action) : Preserves (receiptWGObserved (liftWGPrefix action) record) := by
  intro w ambient h hi
  obtain ⟨tickets,carrier⟩ := hi
  have observed := runWGPrefix_receiptWGObserved (liftWGPrefix action) record w ambient h
  simp only [runWGPrefix_lift] at observed
  simp only [runWGPrefix,runStatePrefix] at observed
  rw [observed]
  cases run : (action.run w).run ambient with
  | error err => exact ⟨[],by simp,True.intro,True.intro⟩
  | ok out =>
    rcases out with ⟨⟨result,v⟩,b⟩
    let receipt := record ⟨result,w,v,ambient,b⟩
    have same := (ProjectedAction.iff_run_ambient _ _ _).mp frame w ambient result v b run
    exact ⟨[receipt],rfl,True.intro,tickets,(carrier.frame same).append [receipt]⟩

theorem submit_preserves (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) (items : List SkbId) :
    Preserves (WorkRoot.submit origin kind pid items) :=
  framed_receipt_preserves _ _ (create_data_frame pid items)

private theorem pure_preserves (x : α) : Preserves (pure x) :=
  StatePrefixEnsures.pure x (fun _ _ _ _ => True.intro) (fun _ _ _ hi => hi)
private theorem chain (g : WGPrefix Event α) (next : α → WGPrefix Event β)
    (hg : Preserves g) (hf : ∀ x, Preserves (next x)) : Preserves (g >>= next) :=
  StatePrefixEnsures.bind hg hf
private theorem loop (xs : List α) (initial : β) (g : α → β → WGPrefix Event (ForInStep β))
    (hg : ∀ x state, Preserves (g x state)) : Preserves (forIn xs initial g) := by
  induction xs generalizing initial with
  | nil => simpa only [List.forIn_nil] using pure_preserves initial
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply StatePrefixEnsures.bind (hg x initial)
    intro step
    cases step with
    | done state => exact pure_preserves state
    | yield state => exact ih state

private theorem choice (p : Prop) [Decidable p] (a b : WGPrefix Event α)
    (ha : Preserves a) (hb : Preserves b) : Preserves (if p then a else b) := by split <;> assumption

elab "send_queue_choice" : tactic => do
  let target ← Lean.Meta.withReducible (Lean.Meta.whnf (← Lean.Elab.Tactic.getMainTarget))
  unless target.isAppOf ``StatePrefixEnsures do Lean.throwError "expected prefix contract"
  let args := target.getAppArgs
  unless args[args.size - 2]!.isAppOf ``ite do Lean.throwError "expected choice"
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply choice))

macro "send_queue_step" : tactic => `(tactic| first
  | with_reducible exact enqueue_preserves _ _ _
  | with_reducible exact submit_preserves _ _ _ _
  | with_reducible exact lift_preserves (key_read_frame _)
  | with_reducible exact lift_preserves (key_write_frame _ _)
  | with_reducible exact lift_preserves (key_put_frame _ _)
  | with_reducible exact lift_preserves (key_get_frame _)
  | with_reducible exact lift_preserves dev_read_frame
  | with_reducible exact lift_preserves (packet_allocation_frame _)
  | with_reducible exact lift_preserves (index_owner_frame _)
  | with_reducible exact lift_preserves (ecn_frame _)
  | with_reducible exact lift_preserves (peer_read_frame _)
  | with_reducible exact lift_preserves (peer_write_frame _ _)
  | with_reducible exact lift_preserves (peer_get_frame _)
  | with_reducible exact lift_preserves (peer_put_frame _)
  | with_reducible exact lift_preserves (branch_expired_frame _ _ _ _)
  | with_reducible exact lift_preserves (ambient_frame _)
  | with_reducible exact pure_preserves _
  | with_reducible apply loop
  | with_reducible apply chain
  | contradiction
  | split
  | send_queue_choice
  | (session_origin_intro_forall; try dsimp only)
  | simp +failIfUnchanged only [bind_assoc,pure_bind])

theorem queued_preserves (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) (retry : Bool) :
    Preserves (WorkRoot.queued origin kind pid retry) := by
  unfold WorkRoot.queued
  simp only [branch,peekQueuedUnit,recordQueued]
  repeat' send_queue_step

theorem noKey_preserves (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) (packets : List WG.Packet)
    (kp : Option KeypairId) (invalid : Bool) : Preserves (WorkRoot.noKey origin kind pid packets kp invalid) := by
  unfold WorkRoot.noKey
  cases invalid <;> cases kp <;> simp only [Bool.false_eq_true,↓reduceIte,branch,invariant]
  all_goals repeat' first | with_reducible exact queued_preserves _ _ _ _ | send_queue_step

theorem key_preserves (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) (id : KeypairId)
    (packets : List WG.Packet) : Preserves (WorkRoot.key origin kind pid id packets) := by
  unfold WorkRoot.key
  simp only [branch,branchCmp]
  repeat' first | with_reducible exact noKey_preserves _ _ _ _ _ _ | send_queue_step

theorem staging_preserves (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) :
    Preserves (WorkRoot.staging origin kind pid) := by
  unfold WorkRoot.staging
  simp only [branch,invariant]
  repeat' first
    | with_reducible exact noKey_preserves _ _ _ _ _ _
    | with_reducible exact key_preserves _ _ _ _ _
    | send_queue_step

theorem keepalive_preserves (origin : Nat) (pid : PeerId) : Preserves (WorkRoot.keepalive origin pid) := by
  unfold WorkRoot.keepalive
  simp only [branch,hiddenAlloc]
  repeat' first | with_reducible exact staging_preserves _ _ _ | send_queue_step

end Leanux.Proofs.WG.AuthenticatedEffects.SendWorkCauses
