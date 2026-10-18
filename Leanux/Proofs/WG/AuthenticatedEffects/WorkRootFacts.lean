import Leanux.Proofs.WG.AuthenticatedEffects.WorkRootProjection
import Leanux.Proofs.WG.AuthenticatedEffects.TimerRootClaims

/-! Each queued-work write and crypt submission inherits its own enclosing
callback occurrence; native refusal branches emit no fabricated work. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.WorkRoot
open Leanux Leanux.WG Leanux.Proofs.Logged Origins.HandshakeSources TimerRoot
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def works : Event → Option Unit
  | .queued _ | .submitted _ => some ()
  | .base _ | .armed _ => none

def Checked (pre : List Event) : Event → Prop
  | .queued r => Seen r.origin r.kind r.peer pre ∧ r.Native
  | .submitted r => Seen r.origin r.kind r.peer pre ∧ r.Native
  | .base _ | .armed _ => True

def Safe (h : List Event) : Prop := ∀ pre e post, h = pre ++ e :: post → Checked pre e
abbrev Inv (h : List Event) (_ : WGWorld) (_ : Ambient) := Safe h
abbrev Preserves (g : WGPrefix Event α) := StatePrefixPreserves Inv Safe g
abbrev Ready (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId)
    (h : List Event) (_ : WGWorld) (_ : Ambient) := Safe h ∧ Seen origin kind pid h

private theorem seen_append (seen : Seen origin kind pid h) (s : List Event) : Seen origin kind pid (h ++ s) := by
  obtain ⟨bound,_⟩ := List.getElem?_eq_some_iff.mp seen
  change (history (h ++ s))[origin]? = _
  simp only [history,List.filterMap_append]
  change (history h ++ history s)[origin]? = _
  rw [List.getElem?_append_left bound]
  exact seen

private theorem append (safe : Safe h)
    (fresh : ∀ pre e post, s = pre ++ e :: post → Checked (h ++ pre) e) : Safe (h ++ s) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.HistorySupport.«0».Leanux.Proofs.WG.Origins.HistorySupport.positions_append)
    Checked h s safe fresh

private theorem append_quiet (safe : Safe h) (quiet : s.filterMap works = []) : Safe (h ++ s) := by
  apply append safe
  intro pre e post position
  cases e with
  | base e => trivial
  | armed r => trivial
  | queued r =>
    have member : Event.queued r ∈ s := by rw [position]; simp
    have found : () ∈ s.filterMap works := List.mem_filterMap.mpr ⟨_,member,rfl⟩
    simp [quiet] at found
  | submitted r =>
    have member : Event.submitted r ∈ s := by rw [position]; simp
    have found : () ∈ s.filterMap works := List.mem_filterMap.mpr ⟨_,member,rfl⟩
    simp [quiet] at found

private theorem append_checked (safe : Safe h) (event : Event) (checked : Checked h event) : Safe (h ++ [event]) := by
  apply append safe
  intro pre e post position
  cases pre with
  | nil => cases position; simpa using checked
  | cons x xs =>
    have lengths := congrArg List.length position
    simp only [List.length_append,List.length_cons,List.length_nil] at lengths
    omega

private theorem lift (a : WG.M α) : Preserves (liftWGPrefix a) :=
  StatePrefixEnsures.lift a (fun _ _ _ hi => hi) (fun _ _ _ _ _ _ hi _ => hi)
private theorem pure (x : α) : Preserves (Pure.pure x) :=
  StatePrefixEnsures.pure x (fun _ _ _ hi => hi) (fun _ _ _ hi => hi)
private theorem lift_ready (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) (a : WG.M α) :
    StatePrefixPreserves (Ready origin kind pid) Safe (liftWGPrefix a) :=
  StatePrefixEnsures.lift a (fun _ _ _ hi => hi.1) (fun _ _ _ _ _ _ hi _ => hi)
private theorem pure_ready (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) (x : α) :
    StatePrefixPreserves (Ready origin kind pid) Safe (Pure.pure x) :=
  StatePrefixEnsures.pure x (fun _ _ _ hi => hi.1) (fun _ _ _ hi => hi)

private theorem old_safe (a : WGPrefix HandshakeCausal.Event α) : Preserves (old a) := by
  intro w ambient h hi
  let suffix := ((runWGPrefix a w ambient (history h)).2.drop (history h).length).map Event.base
  have hs : (runWGPrefix (old a) w ambient h).2 = h ++ suffix := rfl
  have safe : Safe (h ++ suffix) := append_quiet hi
    (filterMap_disjoint Event.base works (fun _ => rfl) _)
  refine ⟨suffix,hs,hs ▸ safe,?_⟩
  cases hr : (runPrefix ((old a).run w) ambient h).1 with
  | error err => trivial
  | ok out => exact hs ▸ safe

private theorem enter_safe (kind : HandshakeCausal.Kind) (pid : PeerId) :
    StatePrefixEnsures Inv Safe (enter kind pid) (fun origin => Ready origin kind pid) := by
  intro w ambient h hi
  have hs : Safe (h ++ [.base (.callback kind pid)]) := append_quiet hi rfl
  refine ⟨[.base (.callback kind pid)],rfl,hs,hs,?_⟩
  change (history (h ++ [.base (.callback kind pid)]))[(history h).length]? = _
  simp [history,base]

private theorem record_ready (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId)
    (action : WG.M Unit) (record : WGRunWitness Unit → Event)
    (good : ∀ h r, Seen origin kind pid h → r.Valid action → Checked h (record r)) :
    StatePrefixPreserves (Ready origin kind pid) Safe
      (receiptWGObserved (liftWGPrefix action) record) := by
  unfold receiptWGObserved
  change StatePrefixPreserves (Ready origin kind pid) Safe (do
    let r ← captureWGRun action
    emitStatePrefix (record r)
    return r.value)
  apply StatePrefixEnsures.bind (StatePrefixEnsures.captureWGRun
    (P := Ready origin kind pid) (S := Safe)
    (Q := fun r h _ _ => Safe h ∧ Seen origin kind pid h ∧ r.Valid action)
    action (fun _ _ _ hi => hi.1) (fun _ _ _ _ _ _ hi native => ⟨hi.1,hi.2,native⟩))
  intro r
  apply StatePrefixEnsures.bind (StatePrefixEnsures.emit
    (P := fun h _ _ => Safe h ∧ Seen origin kind pid h ∧ r.Valid action)
    (S := Safe) (Q := fun _ => Ready origin kind pid) (record r)
    (fun h _ _ hi => append_checked hi.1 (record r) (good h r hi.2.1 hi.2.2))
    (fun h _ _ hi => ⟨append_checked hi.1 (record r) (good h r hi.2.1 hi.2.2),seen_append hi.2.1 _⟩))
  intro doneUnit
  exact pure_ready _ _ _ _

theorem enqueue_ready (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) :
    StatePrefixPreserves (Ready origin kind pid) Safe (enqueue origin kind pid) :=
  record_ready _ _ _ _ _ (fun _ _ seen native => ⟨seen,native⟩)
theorem submit_ready (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) (items : List SkbId) :
    StatePrefixPreserves (Ready origin kind pid) Safe (submit origin kind pid items) :=
  record_ready _ _ _ _ _ (fun _ _ seen native => ⟨seen,native⟩)

private theorem chain_ready (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId)
    (g : WGPrefix Event α) (next : α → WGPrefix Event β)
    (hg : StatePrefixPreserves (Ready origin kind pid) Safe g)
    (hn : ∀ x, StatePrefixPreserves (Ready origin kind pid) Safe (next x)) :
    StatePrefixPreserves (Ready origin kind pid) Safe (g >>= next) := StatePrefixEnsures.bind hg hn
private theorem loop_ready (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId)
    (xs : List α) (initial : β) (g : α → β → WGPrefix Event (ForInStep β))
    (hg : ∀ x state, StatePrefixPreserves (Ready origin kind pid) Safe (g x state)) :
    StatePrefixPreserves (Ready origin kind pid) Safe (forIn xs initial g) := by
  induction xs generalizing initial with
  | nil => simpa only [List.forIn_nil] using pure_ready origin kind pid initial
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply StatePrefixEnsures.bind (hg x initial)
    intro step
    cases step with
    | done state => exact pure_ready origin kind pid state
    | yield state => exact ih state

private theorem choice {I : List Event → WGWorld → Ambient → Prop} {Q : α → List Event → WGWorld → Ambient → Prop}
    (p : Prop) [Decidable p] (a b : WGPrefix Event α)
    (ha : StatePrefixEnsures I Safe a Q) (hb : StatePrefixEnsures I Safe b Q) :
    StatePrefixEnsures I Safe (if p then a else b) Q := by split <;> assumption

elab "work_root_safe_choice" : tactic => do
  let target ← Lean.Meta.withReducible (Lean.Meta.whnf (← Lean.Elab.Tactic.getMainTarget))
  unless target.isAppOf ``StatePrefixEnsures do Lean.throwError "expected prefix contract"
  let args := target.getAppArgs
  unless args[args.size - 2]!.isAppOf ``ite do Lean.throwError "expected choice"
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply choice))

macro "work_root_ready_step" : tactic => `(tactic| first
  | with_reducible exact lift_ready _ _ _ _
  | with_reducible exact pure_ready _ _ _ _
  | with_reducible apply loop_ready
  | with_reducible apply chain_ready
  | contradiction
  | split
  | work_root_safe_choice
  | (session_origin_intro_forall; try dsimp only)
  | simp +failIfUnchanged only [bind_assoc,pure_bind])

theorem queued_ready (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) (retry : Bool) :
    StatePrefixPreserves (Ready origin kind pid) Safe (queued origin kind pid retry) := by
  unfold queued
  repeat' first | with_reducible exact enqueue_ready _ _ _ | work_root_ready_step

theorem noKey_ready (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) (packets : List Packet)
    (kp : Option KeypairId) (invalid : Bool) :
    StatePrefixPreserves (Ready origin kind pid) Safe (noKey origin kind pid packets kp invalid) := by
  unfold noKey
  cases invalid <;> cases kp <;> simp only [Bool.false_eq_true,↓reduceIte]
  all_goals repeat' first | with_reducible exact queued_ready _ _ _ _ | work_root_ready_step

theorem key_ready (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) (id : KeypairId) (packets : List Packet) :
    StatePrefixPreserves (Ready origin kind pid) Safe (key origin kind pid id packets) := by
  unfold key
  repeat' first
    | with_reducible exact noKey_ready _ _ _ _ _ _
    | with_reducible exact submit_ready _ _ _ _
    | work_root_ready_step

theorem staging_ready (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) :
    StatePrefixPreserves (Ready origin kind pid) Safe (staging origin kind pid) := by
  unfold staging
  repeat' first
    | with_reducible exact noKey_ready _ _ _ _ _ _
    | with_reducible exact key_ready _ _ _ _ _
    | work_root_ready_step

theorem keepalive_ready (origin : Nat) (pid : PeerId) :
    StatePrefixPreserves (Ready origin .keepalive pid) Safe (keepalive origin pid) := by
  unfold keepalive
  repeat' first | with_reducible exact staging_ready _ _ _ | work_root_ready_step

private theorem capture (a : WG.M α) : Preserves (captureWGRun a) :=
  StatePrefixEnsures.captureWGRun a (fun _ _ _ hi => hi) (fun _ _ _ _ _ _ hi _ => hi)
private theorem chain (g : WGPrefix Event α) (next : α → WGPrefix Event β)
    (hg : Preserves g) (hn : ∀ x, Preserves (next x)) : Preserves (g >>= next) := StatePrefixEnsures.bind hg hn

private theorem quiet_arm (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId)
    (timer : PeerTimer) (delay : Nat) (caller : Option UInt64) : Preserves (TimerRoot.arm origin kind pid timer delay caller) := by
  unfold TimerRoot.arm receiptWGObserved
  change Preserves (do
    let r ← captureWGRun (armTimer pid timer delay caller)
    emitStatePrefix (Event.armed ⟨origin,kind,pid,timer,delay,caller,r⟩)
    return r.value)
  apply chain _ _ (capture _)
  intro r
  apply chain _ _ (StatePrefixEnsures.emit
    (P := Inv) (S := Safe) (Q := fun _ => Inv) (.armed ⟨origin,kind,pid,timer,delay,caller,r⟩)
    (fun _ _ _ hi => append_checked hi _ True.intro) (fun _ _ _ hi => append_checked hi _ True.intro))
  intro doneUnit
  exact pure _

private theorem quiet_modify (origin : Nat) (kind : HandshakeCausal.Kind) (site : HiddenSite)
    (pid : PeerId) (timer : PeerTimer) (delay : Nat) : Preserves (modifyTimer origin kind site pid timer delay) := by
  unfold modifyTimer
  apply chain _ _ (lift _)
  intro jc
  apply chain _ _ (lift _)
  intro guard
  split
  · exact chain _ _ (quiet_arm _ _ _ _ _ _) (fun _ => pure _)
  · exact pure _
private theorem quiet_derived (origin : Nat) (pid : PeerId) : Preserves (derived origin pid) := by
  unfold derived
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  exact chain _ _ (quiet_modify _ _ _ _ _ _) (fun _ => pure _)
private theorem quiet_traversal (origin : Nat) (pid : PeerId) : Preserves (traversal origin pid) := by
  unfold traversal
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  apply chain _ _ (lift _)
  intro peer
  apply chain _ _ (lift _)
  intro guard
  split
  · exact chain _ _ (quiet_modify _ _ _ _ _ _) (fun _ => pure _)
  · exact pure _

private theorem call_plain (kind : HandshakeCausal.Kind) (pid : PeerId) (body : Nat → WGPrefix Event α)
    (hb : ∀ origin, Preserves (body origin)) : Preserves (TimerRoot.call kind pid body) := by
  apply StatePrefixEnsures.bind (enter_safe kind pid)
  intro origin
  exact (hb origin).consequence (fun _ _ _ hi => hi.1) (fun _ _ _ _ hi => hi)
private theorem call_keepalive (pid : PeerId) :
    Preserves (TimerRoot.call .keepalive pid (fun origin => keepalive origin pid)) := by
  apply StatePrefixEnsures.bind (enter_safe .keepalive pid)
  intro origin
  exact (keepalive_ready origin pid).consequence (fun _ _ _ hi => hi) (fun _ _ _ _ hi => hi.1)

theorem responseWith_safe (mac : HandshakeMac) (pid : PeerId) : Preserves (responseWith (ops mac) pid) := by
  unfold responseWith
  simp only [ops,TimerRoot.ops]
  repeat' first
    | with_reducible exact old_safe _
    | with_reducible exact call_keepalive _
    | with_reducible exact call_plain _ _ _ (fun _ => quiet_derived _ _)
    | with_reducible exact call_plain _ _ _ (fun _ => quiet_traversal _ _)
    | with_reducible exact lift _
    | with_reducible exact pure _
    | with_reducible apply chain
    | split
    | work_root_safe_choice
    | (session_origin_intro_forall; try dsimp only)
    | simp +failIfUnchanged only [bind_assoc,pure_bind]
  all_goals try simp_all only [Option.some.injEq]

elab "work_root_response_safe" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.isAppOf ``Preserves do Lean.throwError "expected preservation"
  unless target.getAppArgs.back!.isAppOf ``responseWith do Lean.throwError "expected response"
  Lean.Elab.Tactic.evalTactic (← `(tactic| exact responseWith_safe _ _))

theorem afterMac_safe (mac : HandshakeMac) (msg : Key) (src : SkbSource) (loaded : Bool) (state : MacState) :
    Preserves (afterMacWith (ops mac) msg src loaded state) := by
  unfold afterMacWith
  simp only [ops,TimerRoot.ops]
  repeat' first
    | work_root_response_safe
    | with_reducible exact old_safe _
    | with_reducible exact call_keepalive _
    | with_reducible exact call_plain _ _ _ (fun _ => quiet_derived _ _)
    | with_reducible exact call_plain _ _ _ (fun _ => quiet_traversal _ _)
    | with_reducible exact lift _
    | with_reducible exact pure _
    | with_reducible apply chain
    | split
    | work_root_safe_choice
    | (session_origin_intro_forall; try dsimp only)
    | simp +failIfUnchanged only [bind_assoc,pure_bind]
  all_goals try simp_all only [Option.some.injEq]

theorem receive_safe (msg : Key) (src : SkbSource) : Preserves (receive msg src) := by
  unfold receive
  apply chain _ _ (lift _)
  intro cookie
  split
  · exact chain _ _ (lift _) (fun _ => pure _)
  · apply chain _ _ (lift _)
    intro loaded
    apply chain _ _ (capture _)
    intro checked
    exact afterMac_safe _ _ _ _ _

end Leanux.Proofs.WG.AuthenticatedEffects.WorkRoot
