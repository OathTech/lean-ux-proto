import Leanux.Proofs.WG.AuthenticatedEffects.WorkTimerFrames
import Leanux.Proofs.WG.AuthenticatedEffects.WorkRootClaims

/-! The combined native receiver journal retains the authenticated cause of
each actual timer-arm occurrence, including before a later internal Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.WorkTimer
open Leanux Leanux.WG Leanux.Proofs.Logged TimerRoot Origins.HandshakeSources
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

private theorem quiet_safe {action : WGPrefix Event α} (appends : StateAppends action)
    (frame : StateHistoryFrame arms action) : TimerRoot.Preserves action := by
  intro w a h hi
  obtain ⟨suffix,hs⟩ := appends w a h
  have same := frame w a h
  rw [hs,List.filterMap_append] at same
  have empty : suffix.filterMap arms = [] := by
    have sizes := congrArg List.length same
    simp only [List.length_append] at sizes
    exact List.eq_nil_of_length_eq_zero (by omega)
  have safe : Safe (h ++ suffix) :=
    (pinned_const _private.Leanux.Proofs.WG.AuthenticatedEffects.TimerRootFacts.«0».Leanux.Proofs.WG.AuthenticatedEffects.TimerRoot.append_quiet) hi empty
  refine ⟨suffix,hs,hs ▸ safe,?_⟩
  cases result : (runPrefix (action.run w) a h).1 with
  | error err => trivial
  | ok value => exact hs ▸ safe

private theorem keepalive_safe (origin : Nat) (pid : PeerId) :
    TimerRoot.Preserves (WorkRoot.keepalive origin pid) :=
  quiet_safe (WorkRoot.keepalive_appends origin pid) (WorkRoot.keepalive_arms_frame origin pid)

private theorem call_keepalive_safe (pid : PeerId) :
    TimerRoot.Preserves (call .keepalive pid (fun origin => WorkRoot.keepalive origin pid)) := by
  apply StatePrefixEnsures.bind (enter_safe .keepalive pid)
  intro origin
  exact (keepalive_safe origin pid).consequence (fun _ _ _ hi => hi.1) (fun _ _ _ _ hi => hi)

private theorem old_safe (action : WGPrefix HandshakeCausal.Event α) : TimerRoot.Preserves (old action) :=
  (pinned_const _private.Leanux.Proofs.WG.AuthenticatedEffects.TimerRootFacts.«0».Leanux.Proofs.WG.AuthenticatedEffects.TimerRoot.old_safe) action
private theorem lift_safe (action : WG.M α) : TimerRoot.Preserves (liftWGPrefix action) :=
  (pinned_const _private.Leanux.Proofs.WG.AuthenticatedEffects.TimerRootFacts.«0».Leanux.Proofs.WG.AuthenticatedEffects.TimerRoot.lift) action
private theorem pure_safe (value : α) : TimerRoot.Preserves (pure value) :=
  (pinned_const _private.Leanux.Proofs.WG.AuthenticatedEffects.TimerRootFacts.«0».Leanux.Proofs.WG.AuthenticatedEffects.TimerRoot.pure) value
private theorem chain (action : WGPrefix Event α) (next : α → WGPrefix Event β)
    (ha : TimerRoot.Preserves action) (hn : ∀ x, TimerRoot.Preserves (next x)) :
    TimerRoot.Preserves (action >>= next) := StatePrefixEnsures.bind ha hn
private theorem choice (p : Prop) [Decidable p] (a b : WGPrefix Event α)
    (ha : TimerRoot.Preserves a) (hb : TimerRoot.Preserves b) :
    TimerRoot.Preserves (if p then a else b) := by split <;> assumption
private theorem call_safe (kind : HandshakeCausal.Kind) (pid : PeerId)
    (body : Nat → WGPrefix Event α)
    (hb : ∀ origin, StatePrefixPreserves (Ready origin kind pid) Safe (body origin)) :
    TimerRoot.Preserves (call kind pid body) :=
  (pinned_const _private.Leanux.Proofs.WG.AuthenticatedEffects.TimerRootFacts.«0».Leanux.Proofs.WG.AuthenticatedEffects.TimerRoot.call_safe) kind pid body hb

elab "work_timer_safe_choice" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.isAppOf ``TimerRoot.Preserves do Lean.throwError "expected timer safety"
  unless target.getAppArgs.back!.isAppOf ``ite do Lean.throwError "expected choice"
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply choice))
macro "work_timer_safe_step" : tactic => `(tactic| first
  | with_reducible exact old_safe _
  | with_reducible exact call_keepalive_safe _
  | with_reducible exact call_safe _ _ _ (fun _ => derived_safe _ _)
  | with_reducible exact call_safe _ _ _ (fun _ => traversal_safe _ _)
  | with_reducible exact lift_safe _
  | with_reducible exact pure_safe _
  | with_reducible apply chain
  | split
  | work_timer_safe_choice
  | (session_origin_intro_forall; try dsimp only)
  | simp +failIfUnchanged only [bind_assoc,pure_bind])

theorem response_safe (mac : HandshakeMac) (pid : PeerId) :
    TimerRoot.Preserves (responseWith (WorkRoot.ops mac) pid) := by
  unfold responseWith
  simp only [WorkRoot.ops,TimerRoot.ops]
  repeat' work_timer_safe_step
  all_goals try simp_all only [Option.some.injEq]
elab "work_timer_response_safe" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.isAppOf ``TimerRoot.Preserves do Lean.throwError "expected timer safety"
  unless target.getAppArgs.back!.isAppOf ``responseWith do Lean.throwError "expected response"
  Lean.Elab.Tactic.evalTactic (← `(tactic| exact response_safe _ _))

theorem afterMac_safe (mac : HandshakeMac) (msg : Key) (src : SkbSource) (loaded : Bool) (state : MacState) :
    TimerRoot.Preserves (afterMacWith (WorkRoot.ops mac) msg src loaded state) := by
  unfold afterMacWith
  simp only [WorkRoot.ops,TimerRoot.ops]
  repeat' first | work_timer_response_safe | work_timer_safe_step
  all_goals try simp_all only [Option.some.injEq]

theorem receive_safe (msg : Key) (src : SkbSource) : TimerRoot.Preserves (WorkRoot.receive msg src) := by
  unfold WorkRoot.receive
  apply chain _ _ (lift_safe _)
  intro cookie
  split
  · exact chain _ _ (lift_safe _) (fun _ => pure_safe _)
  · apply chain _ _ (lift_safe _)
    intro loaded
    apply chain _ _ (StatePrefixEnsures.captureWGRun _ (fun _ _ _ hi => hi)
      (fun _ _ _ _ _ _ hi _ => hi))
    intro checked
    exact afterMac_safe _ _ _ _ _

theorem armed_authenticated (msg : Key) (src : SkbSource) (w : WGWorld) (a : Ambient)
    (pre post : List Event) (r : Arm)
    (position : (runWGPrefix (WorkRoot.receive msg src) w a []).2 = pre ++ .armed r :: post) :
    r.Native ∧ WorkRoot.AuthenticatedAt pre r.origin r.kind r.peer := by
  have empty : Safe [] := by
    intro before event after position
    have size := congrArg List.length position
    simp only [List.length_nil,List.length_append,List.length_cons] at size
    omega
  obtain ⟨suffix,full,safe,_⟩ := receive_safe msg src w a [] empty
  obtain ⟨seen,native⟩ := safe pre (.armed r) post position
  exact ⟨native,
    (pinned_const _private.Leanux.Proofs.WG.AuthenticatedEffects.WorkRootClaims.«0».Leanux.Proofs.WG.AuthenticatedEffects.WorkRoot.callback_from_index)
      msg src w a pre post (.armed r) rfl position r.origin r.kind r.peer seen⟩

end Leanux.Proofs.WG.AuthenticatedEffects.WorkTimer
