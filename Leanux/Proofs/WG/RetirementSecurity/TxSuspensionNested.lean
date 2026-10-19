import Leanux.Proofs.WG.RetirementSecurity.TxWorkRouteControls

/-! Suspension frames through the file/Task/Ambient state stack. Every
nonstructural ambient effect needs its own proved frame; arbitrary task or
ambient computations are not classified as quiet. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension.Nested
open Leanux Leanux.Proofs.Framing Lifetimes Queues

def Keeps (action : StateT S (StateT T AmbientM) α) : Prop :=
  ∀s,TxSuspension.Keeps (action.run s)

theorem pure (value : α) : Keeps (Pure.pure value : StateT S (StateT T AmbientM) α) :=
  fun _=>TxSuspension.pure _

theorem bind {action : StateT S (StateT T AmbientM) α} {next : α→StateT S (StateT T AmbientM) β}
    (first : Keeps action) (rest : ∀x,Keeps (next x)) : Keeps (action >>= next) := by
  intro s
  exact TxSuspension.bind (first s) (fun out=>rest out.1 out.2)

theorem get : Keeps (MonadStateOf.get : StateT S (StateT T AmbientM) S) :=
  fun _=>TxSuspension.pure _

theorem modify (f : S→S) : Keeps (_root_.modify f : StateT S (StateT T AmbientM) Unit) :=
  fun _=>TxSuspension.pure _

theorem set (value : S) : Keeps (MonadStateOf.set value : StateT S (StateT T AmbientM) Unit) :=
  fun _=>TxSuspension.pure _

theorem stopped (stop : Stop) : Keeps (throw stop : StateT S (StateT T AmbientM) α) :=
  fun _=>TxSuspension.stopped _

theorem lift {action : StateT T AmbientM α} (frame : TxSuspension.Keeps action) :
    Keeps (monadLift action : StateT S (StateT T AmbientM) α) := by
  intro s
  change TxSuspension.Keeps (action >>= fun value=>Pure.pure (value,s))
  exact TxSuspension.bind frame (fun _=>TxSuspension.pure _)

theorem list (xs : List α) (initial : β) (body : α→β→StateT S (StateT T AmbientM) (ForInStep β))
    (each : ∀x b,Keeps (body x b)) : Keeps (forIn xs initial body) := by
  induction xs generalizing initial with
  | nil=>exact pure initial
  | cons x xs ih=>
    rw [List.forIn_cons]
    apply bind (each x initial)
    intro step
    cases step with
    | done value=>exact pure value
    | yield value=>exact ih value

theorem map (f : α→β) {action : StateT S (StateT T AmbientM) α} (frame : Keeps action) :
    Keeps (f <$> action) := by
  rw [← bind_pure_comp]
  exact bind frame (fun value=>pure (f value))

theorem discard {action : StateT S (StateT T AmbientM) α} (frame : Keeps action) :
    Keeps (Functor.discard action) := map (fun _=>()) frame

theorem conditional (c : Prop) [Decidable c] (yes no : StateT S (StateT T AmbientM) α)
    (positive : c→Keeps yes) (negative : ¬c→Keeps no) : Keeps (if c then yes else no) := by
  by_cases h:c
  · rw [ite_eq_left h]; exact positive h
  · rw [ite_eq_right h]; exact negative h

theorem dependent_conditional (c : Prop) [Decidable c]
    (yes : c→StateT S (StateT T AmbientM) α) (no : ¬c→StateT S (StateT T AmbientM) α)
    (positive : ∀h,Keeps (yes h)) (negative : ∀h,Keeps (no h)) : Keeps (if h:c then yes h else no h) := by
  by_cases h:c
  · rw [dite_eq_left h]; exact positive h
  · rw [dite_eq_right h]; exact negative h

open Lean Meta Elab Tactic in
elab "nested_suspension_head " name:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Keeps do throwError "not an ambient-suspension contract"
  let some raw := target.getAppArgs.back? | throwError "missing source action"
  let action := raw.consumeMData.headBeta
  let expected ← realizeGlobalConstNoOverloadWithInfo name
  unless action.getAppFn.constName? == some expected do throwError "different source head"

open Lean Meta Elab Tactic in
elab "nested_suspension_intro" : tactic => withMainContext do
  let target := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  unless target.isForall do throwError "not a source continuation"
  evalTactic (← `(tactic| intro x))

/- Share the mirror's compiler-generated continuations once, as in the
existing source-frame tactics; expanding each guard duplicates timer arms. -/
open Lean Meta Elab Tactic in
elab "nested_suspension_reduce" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Keeps do throwError "not an ambient-suspension contract"
  let .app property action := target | throwError "missing source action"
  let action := action.consumeMData
  if let .letE name ty value body _ := action then
    if name.toString.startsWith "__do_jp" then
      let claim ← forallTelescope ty fun args _ =>
        mkForallFVars args (mkApp property (mkAppN value args))
      let proof ← mkFreshExprSyntheticOpaqueMVar claim
      let (continuation, next) ← withLocalDeclD name ty fun f => do
        let claim ← forallTelescope ty fun args _ =>
          mkForallFVars args (mkApp property (mkAppN f args))
        withLocalDeclD `nested_suspension_join claim fun hf => do
          let next ← mkFreshExprSyntheticOpaqueMVar (mkApp property (body.instantiate1 f))
          return (← mkLambdaFVars #[f, hf] next, next.mvarId!)
      goal.assign (mkApp2 continuation value proof)
      replaceMainGoal [proof.mvarId!,next]
    else
      replaceMainGoal [← goal.replaceTargetDefEq (mkApp property (body.instantiate1 value))]
    return
  if let .letE _ _ value body _ := action.getAppFn.consumeMData then
    replaceMainGoal [← goal.replaceTargetDefEq
      (mkApp property (mkAppN (body.instantiate1 value) action.getAppArgs))]
    return
  let reduced := action.headBeta
  if !Expr.equal action reduced then
    replaceMainGoal [← goal.replaceTargetDefEq (mkApp property reduced)]
    return
  if action.getAppFn.isFVar then
    for decl in ← getLCtx do
      if decl.userName == `nested_suspension_join then
        let proof := mkAppN decl.toExpr action.getAppArgs
        if ← withReducible (isDefEq (← inferType proof) target) then
          goal.assign proof
          replaceMainGoal []
          return
  let head := action.getAppFn.constName?
  if head == some ``ite then
    evalTactic (← `(tactic| apply TxSuspension.Nested.conditional))
    return
  if head == some ``dite then
    evalTactic (← `(tactic| apply TxSuspension.Nested.dependent_conditional))
    return
  if (← Lean.Meta.matchMatcherApp? action).isSome then
    replaceMainGoal (← Lean.Meta.Split.splitMatch goal action)
    return
  throwError "not a source continuation reduction"

macro "nested_suspension_step" : tactic => `(tactic| first
  | nested_suspension_reduce
  | (nested_suspension_head liftM; unfold liftM)
  | (nested_suspension_head Bind.bind; apply TxSuspension.Nested.bind)
  | (nested_suspension_head Pure.pure; exact TxSuspension.Nested.pure _)
  | (nested_suspension_head MonadStateOf.get; exact TxSuspension.Nested.get)
  | (nested_suspension_head MonadState.get; exact TxSuspension.Nested.get)
  | (nested_suspension_head _root_.modify; exact TxSuspension.Nested.modify _)
  | (nested_suspension_head MonadStateOf.set; exact TxSuspension.Nested.set _)
  | (nested_suspension_head MonadExceptOf.throw; exact TxSuspension.Nested.stopped _)
  | (nested_suspension_head MonadExcept.throw; exact TxSuspension.Nested.stopped _)
  | (nested_suspension_head ForIn.forIn; first | apply TxSuspension.Nested.list | rw [Std.Legacy.Range.forIn_eq_forIn_range'])
  | (nested_suspension_head Functor.map; apply TxSuspension.Nested.map)
  | (nested_suspension_head Functor.discard; apply TxSuspension.Nested.discard)
  | nested_suspension_intro)

/- Reuse the source-step calculus while keeping every nonstructural leaf
contract named at its call site. -/
macro "nested_suspension_source" "[" fs:ident,* "]" "using" "[" facts:ident,* "]" : tactic => do
  let mut use ← `(tactic| fail "no named suspension frame")
  for fact in facts.getElems.reverse do
    use ← `(tactic| first | env_operation_fact $fact | ($use:tactic))
  let names := fs.getElems.map fun f=>
    if f.getId.toString.startsWith "_private." then Lean.mkCIdent (normalizePinnedName f.getId) else f
  let expand ← if names.isEmpty then `(tactic| skip) else `(tactic| unfold $names:ident*)
  `(tactic| ($expand; repeat' first | ($use:tactic) | nested_suspension_step))

theorem ambient {action : AmbientM α} (frame : SameView Ambient.suspended action) :
    Keeps (monadLift action : StateT S (StateT T AmbientM) α) :=
  lift (TxSuspension.ambient frame)

theorem branch (decision : Decision) (value : Bool) :
    Keeps (Leanux.branch decision value : StateT S (StateT T AmbientM) Bool) :=
  lift (TxSuspension.branch decision value)

theorem compare (decision : Decision) (value : Bool) (a b : Int) :
    Keeps (branchCmp decision value a b : StateT S (StateT T AmbientM) Bool) :=
  lift (TxSuspension.compare decision value a b)

theorem invariant (message : String) :
    Keeps (Leanux.invariant message : StateT S (StateT T AmbientM) α) :=
  lift (TxSuspension.invariant message)

theorem unsupported (message : String) :
    Keeps (Leanux.unsupported message : StateT S (StateT T AmbientM) α) :=
  lift (TxSuspension.unsupported message)

theorem hidden (site : HiddenSite) :
    Keeps (Leanux.hidden site : StateT S (StateT T AmbientM) (List UInt8)) :=
  lift (TxSuspension.hidden site)

theorem allocation (site : AllocSite) :
    Keeps (hiddenAlloc site : StateT S (StateT T AmbientM) Bool) :=
  lift (TxSuspension.allocation site)

theorem product_fs {action : FS.M α} (frame : Keeps action) :
    SameView TxSuspension.suspended (liftFS action) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  change (do let (((r,s),t),a)←((action.run w.fs).run w.tasks).run w.ambient
             Pure.pure (r,{w with fs:=s,tasks:=t,ambient:=a}))=.ok (result,v) at run
  cases native:((action.run w.fs).run w.tasks).run w.ambient with
  | error reason=>simp only [native] at run; cases run
  | ok out=>
    simp only [native] at run
    cases run
    exact TxSuspension.native (frame w.fs) native

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension.Nested
