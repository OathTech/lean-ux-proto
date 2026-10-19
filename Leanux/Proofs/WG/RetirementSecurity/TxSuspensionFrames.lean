import Leanux.Proofs.WG.RetirementSecurity.TxActorScheduler

/-! Inner-Ambient frames for native subsystem calls. Keeping the actual
suspended records is separate from preserving the WGWorld projection; an
arbitrary ambient action is deliberately not admitted by these rules. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

def Keeps (action : StateT S AmbientM α) : Prop :=
  ∀s,SameView Ambient.suspended (action.run s)

theorem pure (value : α) : Keeps (Pure.pure value : StateT S AmbientM α) := by
  intro s
  exact SameView.pure _ _

theorem bind {action : StateT S AmbientM α} {next : α→StateT S AmbientM β}
    (first : Keeps action) (rest : ∀x,Keeps (next x)) : Keeps (action >>= next) := by
  intro s
  change SameView Ambient.suspended (action.run s >>= fun out=>(next out.1).run out.2)
  exact (first s).bind fun out=>rest out.1 out.2

theorem get : Keeps (MonadStateOf.get : StateT S AmbientM S) := by
  intro s
  exact SameView.pure _ _

theorem modify (f : S→S) : Keeps (_root_.modify f : StateT S AmbientM Unit) := by
  intro s
  exact SameView.pure _ _

theorem set (value : S) : Keeps (MonadStateOf.set value : StateT S AmbientM Unit) := by
  intro s
  exact SameView.pure _ _

theorem stopped (stop : Stop) : Keeps (throw stop : StateT S AmbientM α) := by
  intro s initial
  apply (hoare_iff_run _ _ _).mpr
  intro a result b before run
  cases run

theorem ambient {action : AmbientM α} (frame : SameView Ambient.suspended action) :
    Keeps (monadLift action : StateT S AmbientM α) := by
  intro s
  change SameView Ambient.suspended (action >>= fun value=>Pure.pure (value,s))
  exact frame.bind fun _=>SameView.pure _ _

theorem list (xs : List α) (initial : β) (body : α→β→StateT S AmbientM (ForInStep β))
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

theorem map (f : α→β) {action : StateT S AmbientM α} (frame : Keeps action) :
    Keeps (f <$> action) := by
  rw [← bind_pure_comp]
  exact bind frame (fun value=>pure (f value))

theorem discard {action : StateT S AmbientM α} (frame : Keeps action) : Keeps (Functor.discard action) :=
  map (fun _=>()) frame

theorem native {action : StateT S AmbientM α} (frame : Keeps action)
    (run : (action.run s).run a=.ok ((result,t),b)) : b.suspended=a.suspended :=
  (ProjectedAction.iff_run _ _ _).mp (frame s) a (result,t) b run

theorem product {action : WG.M α} (frame : Keeps action) :
    SameView (fun w : World=>w.ambient.suspended) (liftWG action) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  exact native frame (HolderPoll.native_receipt run)

theorem conditional (c : Prop) [Decidable c] (yes no : StateT S AmbientM α)
    (positive : c → Keeps yes) (negative : ¬c → Keeps no) : Keeps (if c then yes else no) := by
  by_cases h : c
  · rw [ite_eq_left h]; exact positive h
  · rw [ite_eq_right h]; exact negative h

theorem dependent_conditional (c : Prop) [Decidable c]
    (yes : c → StateT S AmbientM α) (no : ¬c → StateT S AmbientM α)
    (positive : ∀h,Keeps (yes h)) (negative : ∀h,Keeps (no h)) : Keeps (if h : c then yes h else no h) := by
  by_cases h : c
  · rw [dite_eq_left h]; exact positive h
  · rw [dite_eq_right h]; exact negative h

open Lean Meta Elab Tactic in
elab "suspension_head " name:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Keeps do throwError "not an ambient-suspension contract"
  let some raw := target.getAppArgs.back? | throwError "missing source action"
  let action := raw.consumeMData.headBeta
  let expected ← realizeGlobalConstNoOverloadWithInfo name
  unless action.getAppFn.constName? == some expected do throwError "different source head"

open Lean Meta Elab Tactic in
elab "suspension_intro" : tactic => withMainContext do
  let target := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  unless target.isForall do throwError "not a source continuation"
  evalTactic (← `(tactic| intro x))

/- Share the mirror's compiler-generated continuations once, as in the
existing source-frame tactics; expanding each guard duplicates timer arms. -/
open Lean Meta Elab Tactic in
elab "suspension_reduce" : tactic => withMainContext do
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
        withLocalDeclD `suspension_join claim fun hf => do
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
      if decl.userName == `suspension_join then
        let proof := mkAppN decl.toExpr action.getAppArgs
        if ← withReducible (isDefEq (← inferType proof) target) then
          goal.assign proof
          replaceMainGoal []
          return
  let head := action.getAppFn.constName?
  if head == some ``ite then
    evalTactic (← `(tactic| apply TxSuspension.conditional))
    return
  if head == some ``dite then
    evalTactic (← `(tactic| apply TxSuspension.dependent_conditional))
    return
  if (← Lean.Meta.matchMatcherApp? action).isSome then
    replaceMainGoal (← Lean.Meta.Split.splitMatch goal action)
    return
  throwError "not a source continuation reduction"

macro "suspension_step" : tactic => `(tactic| first
  | suspension_reduce
  | (suspension_head liftM; unfold liftM)
  | (suspension_head Bind.bind; apply TxSuspension.bind)
  | (suspension_head Pure.pure; exact TxSuspension.pure _)
  | (suspension_head MonadStateOf.get; exact TxSuspension.get)
  | (suspension_head MonadState.get; exact TxSuspension.get)
  | (suspension_head _root_.modify; exact TxSuspension.modify _)
  | (suspension_head MonadStateOf.set; exact TxSuspension.set _)
  | (suspension_head MonadExceptOf.throw; exact TxSuspension.stopped _)
  | (suspension_head MonadExcept.throw; exact TxSuspension.stopped _)
  | (suspension_head ForIn.forIn; first | apply TxSuspension.list | rw [Std.Legacy.Range.forIn_eq_forIn_range'])
  | (suspension_head Functor.map; apply TxSuspension.map)
  | (suspension_head Functor.discard; apply TxSuspension.discard)
  | suspension_intro)

/- Reuse the source-step calculus while keeping every nonstructural leaf
contract named at its call site. -/
macro "suspension_source" "[" fs:ident,* "]" "using" "[" facts:ident,* "]" : tactic => do
  let mut use ← `(tactic| fail "no named suspension frame")
  for fact in facts.getElems.reverse do
    use ← `(tactic| first | env_operation_fact $fact | ($use:tactic))
  let expand ← if fs.getElems.isEmpty then `(tactic| skip) else `(tactic| unfold $fs:ident*)
  `(tactic| ($expand; repeat' first | ($use:tactic) | suspension_step))

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension
