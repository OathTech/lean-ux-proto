import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedWheelPointCuts

/-! The canonical source witness expands both kept and enqueued branches;
bookkeeping and cached-peer writes are separate native nodes before validation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Wheel.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal
variable {pid : PeerId} {saved : Peer}

elab "wheel_shape_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a source shape"
  let some action := target.getAppArgs.back? | Lean.throwError "missing source action"
  let .const actual _ := action.consumeMData.headBeta.getAppFn
    | Lean.throwError "not a constant source head"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("." ++ name) do
    Lean.throwError "different source head"

elab "wheel_wg_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a source shape"
  let some action := target.getAppArgs.back? | Lean.throwError "missing action"
  let action := action.consumeMData.headBeta
  let body ← if action.isAppOf ``wg then
      match action.getAppArgs.back? with
      | some body => pure body
      | none => Lean.throwError "missing WG body"
    else do
      unless action.isAppOf ``liftWGObserver do Lean.throwError "not a WG observer"
      let some observer := action.getAppArgs.back? | Lean.throwError "missing observer"
      unless observer.isAppOf ``liftWGPrefix do Lean.throwError "not a native lift"
      let some body := observer.getAppArgs.back? | Lean.throwError "missing body"
      pure body
  let .const actual _ := body.consumeMData.headBeta.getAppFn | Lean.throwError "not a native head"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("." ++ name) do
    Lean.throwError "different native head"

elab "wheel_bound_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not shape"
  let some action := target.getAppArgs.back? | Lean.throwError "missing action"
  let body ← if action.isAppOf ``wg then
      match action.getAppArgs.back? with
      | some body => pure body
      | none => Lean.throwError "missing body"
    else do
      unless action.isAppOf ``liftWGObserver do Lean.throwError "not observer"
      let some observer := action.getAppArgs.back? | Lean.throwError "missing observer"
      unless observer.isAppOf ``liftWGPrefix do Lean.throwError "not native"
      let some body := observer.getAppArgs.back? | Lean.throwError "missing native"
      pure body
  let body := body.consumeMData.headBeta
  unless body.isAppOf ``Bind.bind do Lean.throwError "not bind"
  let args := body.getAppArgs
  let some head := args[args.size - 2]? | Lean.throwError "missing first action"
  let .const actual _ := head.consumeMData.headBeta.getAppFn | Lean.throwError "not constant"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("." ++ name) do
    Lean.throwError "different first action"


theorem wg_bind (action : WG.M α) (next : α → WG.M β) :
    wg (action >>= next) = (wg action >>= fun value => wg (next value)) :=
  Consume.Leaf.wg_bind action next

noncomputable def bindShape (action : WG.M α) (next : α → WG.M β)
    (head : Shape pid saved (wg action)) (tail : ∀ value, Shape pid saved (wg (next value))) :
    Shape pid saved (liftWGObserver (liftWGPrefix (action >>= next))) := by
  change Shape pid saved (wg (action >>= next))
  rw [wg_bind]
  exact .bind head tail

noncomputable def conditionalShape (test : Prop) [Decidable test]
    {left right : PrefixM Event α} (yes : test → Shape pid saved left) (no : ¬test → Shape pid saved right) :
    Shape pid saved (if test then left else right) := by
  split
  · exact yes ‹_›
  · exact no ‹_›

noncomputable def ifShape (test : Prop) [Decidable test] (yes no : WG.M α)
    (left : test → Shape pid saved (wg yes)) (right : ¬test → Shape pid saved (wg no)) :
    Shape pid saved (liftWGObserver (liftWGPrefix (if test then yes else no))) := by
  split
  · exact left ‹_›
  · exact right ‹_›

noncomputable def failedShape (action : WG.M α) (next : α → WG.M β) (failure : Consume.Leaf.Failure (wg action)) :
    Shape pid saved (wg (action >>= next)) := by
  rw [wg_bind]
  exact .failed failure (fun value => wg (next value))

macro "wheel_step " timer:ident : tactic => `(tactic| first
  | (wheel_bound_head «throw»; exact failedShape _ _ (.wgThrow _))
  | (wheel_bound_head invariant; exact failedShape _ _ (.wgInvariant _))
  | (wheel_wg_head setPeer; refine .native (.install _ ?_); cases (show PeerTimer from $timer) <;> exact ⟨rfl,rfl,rfl⟩)
  | (wheel_wg_head getPeer; exact .native (.peer _))
  | (wheel_wg_head get; exact .native .world)
  | (wheel_wg_head modify; exact .native (.stamp _))
  | (wheel_wg_head hidden; exact .native (.ambient _))
  | (wheel_wg_head peekHiddenSite; exact .native (.ambient _))
  | (wheel_wg_head «throw»; exact .native (.failure _))
  | (wheel_wg_head invariant; exact .native (.failure (.invariant _)))
  | (wheel_wg_head Pure.pure; exact .pure _)
  | (wheel_wg_head Bind.bind; apply bindShape)
  | (wheel_wg_head ite; apply ifShape)
  | (wheel_shape_head Bind.bind; apply Shape.bind)
  | (wheel_shape_head Pure.pure; exact .pure _)
  | (wheel_shape_head ite; apply conditionalShape)
  | maintenance_intro
  | split
  | (simp +failIfUnchanged only))

noncomputable def bodyShape (pid : PeerId) (timer : PeerTimer) (expires clock : UInt64)
    (unit : Option Nat) (saved : Peer) : Shape pid saved (wg (body pid timer expires clock unit saved)) := by
  unfold body
  repeat' wheel_step timer

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Wheel.Points
