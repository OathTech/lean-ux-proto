import Leanux.Proofs.WG.AuthenticatedEffects.TimerRootProjection

/-! Each native arm occurrence names its own earlier callback entry. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TimerRoot
open Leanux Leanux.WG Leanux.Proofs.Logged Origins.HandshakeSources
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def arms : Event → Option Arm
  | .base _ => none
  | .armed r => some r

def Seen (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) (h : List Event) : Prop :=
  (history h)[origin]? = some (.callback kind pid)

def Checked (pre : List Event) : Event → Prop
  | .base _ => True
  | .armed r => Seen r.origin r.kind r.peer pre ∧ r.Native

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

private theorem append_quiet (safe : Safe h) (quiet : s.filterMap arms = []) : Safe (h ++ s) := by
  apply append safe
  intro pre e post position
  cases e with
  | base e => trivial
  | armed r =>
    have member : Event.armed r ∈ s := by rw [position]; simp
    have found : r ∈ s.filterMap arms := List.mem_filterMap.mpr ⟨_,member,rfl⟩
    simp [quiet] at found

private theorem append_arm (safe : Safe h) (r : Arm)
    (seen : Seen r.origin r.kind r.peer h) (native : r.Native) : Safe (h ++ [.armed r]) := by
  apply append safe
  intro pre e post position
  cases pre with
  | nil => cases position; exact ⟨by simpa using seen,native⟩
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
    (filterMap_disjoint Event.base arms (fun _ => rfl) _)
  refine ⟨suffix,hs,hs ▸ safe,?_⟩
  cases hr : (runPrefix ((old a).run w) ambient h).1 with
  | error err => trivial
  | ok out => exact hs ▸ safe

theorem enter_safe (kind : HandshakeCausal.Kind) (pid : PeerId) :
    StatePrefixEnsures Inv Safe (enter kind pid) (fun origin => Ready origin kind pid) := by
  intro w ambient h hi
  have hs : Safe (h ++ [.base (.callback kind pid)]) := append_quiet hi rfl
  refine ⟨[.base (.callback kind pid)],rfl,hs,hs,?_⟩
  change (history (h ++ [.base (.callback kind pid)]))[(history h).length]? = _
  simp [history,base]

theorem arm_safe (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId)
    (timer : PeerTimer) (delay : Nat) (caller : Option UInt64) :
    StatePrefixPreserves (Ready origin kind pid) Safe (arm origin kind pid timer delay caller) := by
  unfold arm receiptWGObserved
  change StatePrefixPreserves (Ready origin kind pid) Safe (do
    let r ← captureWGRun (armTimer pid timer delay caller)
    emitStatePrefix (Event.armed ⟨origin,kind,pid,timer,delay,caller,r⟩)
    return r.value)
  apply StatePrefixEnsures.bind (StatePrefixEnsures.captureWGRun
    (P := Ready origin kind pid) (S := Safe)
    (Q := fun r h _ _ => Safe h ∧ Seen origin kind pid h ∧ r.Valid (armTimer pid timer delay caller))
    _ (fun _ _ _ hi => hi.1) (fun _ _ _ _ _ _ hi native => ⟨hi.1,hi.2,native⟩))
  intro r
  apply StatePrefixEnsures.bind (StatePrefixEnsures.emit
    (P := fun h _ _ => Safe h ∧ Seen origin kind pid h ∧ r.Valid (armTimer pid timer delay caller))
    (S := Safe) (Q := fun _ => Ready origin kind pid)
    (Event.armed ⟨origin,kind,pid,timer,delay,caller,r⟩)
    (fun _ _ _ hi => append_arm hi.1 ⟨origin,kind,pid,timer,delay,caller,r⟩ hi.2.1 hi.2.2)
    (fun h _ _ hi => ⟨append_arm hi.1 ⟨origin,kind,pid,timer,delay,caller,r⟩ hi.2.1 hi.2.2,seen_append hi.2.1 _⟩))
  intro doneUnit
  exact pure_ready _ _ _ _

theorem modify_safe (origin : Nat) (kind : HandshakeCausal.Kind) (site : HiddenSite)
    (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    StatePrefixPreserves (Ready origin kind pid) Safe (modifyTimer origin kind site pid timer delay) := by
  unfold modifyTimer
  apply StatePrefixEnsures.bind (lift_ready _ _ _ _)
  intro jc
  apply StatePrefixEnsures.bind (lift_ready _ _ _ _)
  intro guard
  split
  · exact StatePrefixEnsures.bind (arm_safe _ _ _ _ _ _) (fun _ => pure_ready _ _ _ _)
  · exact pure_ready _ _ _ _

theorem derived_safe (origin : Nat) (pid : PeerId) :
    StatePrefixPreserves (Ready origin .sessionDerived pid) Safe (derived origin pid) := by
  unfold derived
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  exact StatePrefixEnsures.bind (modify_safe _ _ _ _ _ _) (fun _ => pure_ready _ _ _ _)

theorem traversal_safe (origin : Nat) (pid : PeerId) :
    StatePrefixPreserves (Ready origin .traversal pid) Safe (traversal origin pid) := by
  unfold traversal
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  apply StatePrefixEnsures.bind (lift_ready _ _ _ _)
  intro peer
  apply StatePrefixEnsures.bind (lift_ready _ _ _ _)
  intro guard
  split
  · exact StatePrefixEnsures.bind (modify_safe _ _ _ _ _ _) (fun _ => pure_ready _ _ _ _)
  · exact pure_ready _ _ _ _

private theorem call_safe (kind : HandshakeCausal.Kind) (pid : PeerId)
    (body : Nat → WGPrefix Event α)
    (hb : ∀ origin, StatePrefixPreserves (Ready origin kind pid) Safe (body origin)) :
    Preserves (call kind pid body) := by
  apply StatePrefixEnsures.bind (enter_safe kind pid)
  intro origin
  exact (hb origin).consequence (fun _ _ _ hi => hi) (fun _ _ _ _ hi => hi.1)

private theorem chain (g : WGPrefix Event α) (next : α → WGPrefix Event β)
    (hg : Preserves g) (hn : ∀ x, Preserves (next x)) : Preserves (g >>= next) := StatePrefixEnsures.bind hg hn
private theorem choice (p : Prop) [Decidable p] (a b : WGPrefix Event α)
    (ha : Preserves a) (hb : Preserves b) : Preserves (if p then a else b) := by split <;> assumption

elab "timer_root_safe_choice" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.isAppOf ``Preserves do Lean.throwError "expected preservation"
  let args := target.getAppArgs
  unless args.back!.isAppOf ``ite do Lean.throwError "expected a choice"
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply choice))

theorem responseWith_safe (mac : HandshakeMac) (pid : PeerId) : Preserves (responseWith (ops mac) pid) := by
  unfold responseWith
  simp only [ops]
  repeat' first
    | with_reducible exact old_safe _
    | with_reducible exact call_safe _ _ _ (fun _ => derived_safe _ _)
    | with_reducible exact call_safe _ _ _ (fun _ => traversal_safe _ _)
    | with_reducible exact lift _
    | with_reducible exact pure _
    | with_reducible apply chain
    | split
    | timer_root_safe_choice
    | (session_origin_intro_forall; try dsimp only)
    | simp +failIfUnchanged only [bind_assoc,pure_bind]
  all_goals try simp_all only [Option.some.injEq]

elab "timer_root_response_safe" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.isAppOf ``Preserves do Lean.throwError "expected preservation"
  unless target.getAppArgs.back!.isAppOf ``responseWith do Lean.throwError "expected response"
  Lean.Elab.Tactic.evalTactic (← `(tactic| exact responseWith_safe _ _))

theorem afterMac_safe (mac : HandshakeMac) (msg : Key) (src : SkbSource) (loaded : Bool) (state : MacState) :
    Preserves (afterMacWith (ops mac) msg src loaded state) := by
  unfold afterMacWith
  simp only [ops]
  repeat' first
    | timer_root_response_safe
    | with_reducible exact old_safe _
    | with_reducible exact call_safe _ _ _ (fun _ => derived_safe _ _)
    | with_reducible exact call_safe _ _ _ (fun _ => traversal_safe _ _)
    | with_reducible exact lift _
    | with_reducible exact pure _
    | with_reducible apply chain
    | split
    | timer_root_safe_choice
    | (session_origin_intro_forall; try dsimp only)
    | simp +failIfUnchanged only [bind_assoc,pure_bind]
  all_goals try simp_all only [Option.some.injEq]

private theorem capture (a : WG.M α) : Preserves (captureWGRun a) :=
  StatePrefixEnsures.captureWGRun a (fun _ _ _ hi => hi) (fun _ _ _ _ _ _ hi _ => hi)

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

end Leanux.Proofs.WG.AuthenticatedEffects.TimerRoot
