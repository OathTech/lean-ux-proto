import Leanux.Proofs.Logged.Runner
import Leanux.Proofs.WG.Keypairs.Evolution.Rules
import Leanux.Proofs.Framing.Product

/-! The explicit-World outer runner carries the proved lifetime invariant
through every actual observed syscall and ambient-record step. -/
namespace Leanux.Proofs.WG.Keypairs.RunnerProof
open Lean Leanux Leanux.Runner Leanux.Proofs.Logged
open Leanux.Proofs.Framing Std.Do

set_option maxHeartbeats 2000000
set_option pp.structureInstances false

theorem runAtLogged_inv_wp {g : GhostM α} (hg : Evolves g)
    (index : Nat) (w : World) :
    ⦃fun h => ⌜Inv (snapshot w.wg) h⌝⦄ runAtLogged index w g
    ⦃⇓? out h => ⌜Inv (snapshot out.2.wg) h⌝⦄ := by
  apply (stateExceptHoare_iff_triple _ _ _).mp
  intro h out h' hp hr
  exact hg.preserves h w out.1 h' out.2 hp
    ((runAtLogged_ok_iff index w g h out.1 h' out.2).mp hr)

theorem ordinary_runAt_inv_wp {a : Leanux.M α} (ha : ProductOrdinaryAction a)
    (index : Nat) (w : World) :
    ⦃fun h => ⌜Inv (snapshot w.wg) h⌝⦄
      (liftM ((a.run w).mapError (fun e => (index, e))) :
        StateT History (Except (Nat × Stop)) (α × World))
    ⦃⇓? out h => ⌜Inv (snapshot out.2.wg) h⌝⦄ := by
  apply (stateExceptHoare_iff_triple _ _ _).mp
  intro h out h' hp hr
  change ((a.run w).mapError (fun e => (index, e)) >>= fun x => pure (x, h)) = .ok (out, h') at hr
  cases he : a.run w with
  | error e => simp [he, Except.mapError] at hr; cases hr
  | ok value =>
    simp [he, Except.mapError] at hr
    rcases hr with ⟨rfl, rfl⟩
    exact ((Lifetimes.ProjectedAction.iff_run _ _ _).mp ha w _ _ he).preserves hp


/-- Choose the current World carried by a runner result; JSON bookkeeping
retains the current history assertion. Only checked Triple rules are built. -/
private def lifetimeRunnerResultAssertion
    (invariant type pre : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let type ← Lean.Meta.whnf type
  Lean.Meta.withLocalDeclD `out type fun out => do
    let world? ←
      if type.isConstOf ``World then pure (some out)
      else if type.isAppOf ``Prod && type.getAppArgs.size == 2 then
        let args := type.getAppArgs
        if args[0]!.isConstOf ``World then pure (some (Lean.mkProj ``Prod 0 out))
        else if args[1]!.isConstOf ``World then pure (some (Lean.mkProj ``Prod 1 out))
        else pure none
      else pure none
    let assertion := match world? with
      | some w => Lean.mkApp invariant w
      | none => pre
    Lean.Meta.mkLambdaFVars #[out] assertion

elab "lifetime_runner_head " name:ident : tactic => do
  let target := (← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)).consumeMData
  unless target.isAppOf ``Triple && target.getAppArgs.size ≥ 3 do
    Lean.throwError "not a runner triple"
  let args := target.getAppArgs
  let action := args[args.size - 3]!.consumeMData
  let expected ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo name
  unless action.getAppFn.isConstOf expected do
    Lean.throwError "different runner action head"

elab "lifetime_runner_step " inv:ident : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  if target.isForall then
    Lean.Elab.Tactic.evalTactic (← `(tactic| intro))
    return
  unless target.isAppOf ``Triple && target.getAppArgs.size ≥ 3 do
    Lean.throwError "not a runner triple"
  let args := target.getAppArgs
  let action := args[args.size - 3]!.consumeMData
  let pre := args[args.size - 2]!
  let invariant ← Lean.Elab.Term.elabTerm inv none
  if action.isAppOf ``Bind.bind then
    let aa := action.getAppArgs
    unless aa.size ≥ 2 do Lean.throwError "missing bind arguments"
    let x := aa[aa.size - 2]!
    let type ← Lean.Meta.inferType x
    let result := type.getAppArgs.back!
    let q ← lifetimeRunnerResultAssertion invariant result pre
    let mut proof ← Lean.Meta.mkConstWithFreshMVarLevels ``Triple.bind
    let mut type ← Lean.Meta.inferType proof
    let mut goals : List Lean.MVarId := []
    while let .forallE name domain body _ := type.consumeMData do
      let argument ←
        match name.toString with
        | "m" => pure args[0]!
        | "ps" => pure args[1]!
        | "α" => pure result
        | "β" => pure args[3]!
        | "P" => pure pre
        | "Q" => pure q
        | "R" => pure args.back!
        | "x" => pure x
        | "f" => pure aa.back!
        | "hx" | "hf" =>
          let hole ← Lean.Meta.mkFreshExprMVar domain
          goals := goals ++ [hole.mvarId!]
          pure hole
        | _ => Lean.Meta.synthInstance domain
      unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType argument) domain do
        Lean.throwError "canonical bind parameter {name} has the wrong type"
      proof := Lean.mkApp proof argument
      type := body.instantiate1 argument
    goal.assign proof
    Lean.Elab.Tactic.replaceMainGoal goals
    return
  if action.isAppOf ``ForIn.forIn then
    let aa := action.getAppArgs
    unless aa.size ≥ 2 do Lean.throwError "missing iterator arguments"
    let init := aa[aa.size - 2]!
    let q ← lifetimeRunnerResultAssertion invariant (← Lean.Meta.inferType init) pre
    let qs ← Lean.PrettyPrinter.delab q
    let qt ← Lean.PrettyPrinter.delab (← Lean.Meta.inferType q)
    let qsyntax ← `(term| ($qs : $qt))
    let err ← Lean.Meta.whnf (Lean.mkProj ``Prod 1 args.back!)
    let esyntax ← Lean.PrettyPrinter.delab err
    let psyntax ← Lean.PrettyPrinter.delab args[1]!
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      apply Triple.entails_wp_of_pre_post (ps := $psyntax) (Q' := ($qsyntax, $esyntax))))
    let rest := (← Lean.Elab.Tactic.getGoals).tail
    Lean.Elab.Tactic.setGoals [(← Lean.Elab.Tactic.getMainGoal)]
    Lean.Elab.Tactic.evalTactic (← `(tactic| rw [← Array.forIn_toList]))
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      apply Spec.forIn_list (fun p => $qsyntax p.2, $esyntax)))
    Lean.Elab.Tactic.evalTactic (← `(tactic| intro pref cur suff cursor acc))
    Lean.Elab.Tactic.setGoals ((← Lean.Elab.Tactic.getGoals) ++ rest)
    return
  if action.isAppOf ``Pure.pure then
    Lean.Elab.Tactic.evalTactic (← `(tactic| apply Triple.pure))
    return
  if action.isAppOf ``MonadExcept.throw || action.isAppOf ``MonadExceptOf.throw then
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      apply Triple.entails_wp_of_pre (Spec.throw_StateT
        (m := Except (Nat × Stop)) (ps := .except (Nat × Stop) .pure) _)))
    return
  if action.isAppOf ``ite || action.isAppOf ``dite then
    Lean.Elab.Tactic.evalTactic (← `(tactic| split))
    return
  let rec head : Nat → Lean.Expr → Lean.Expr
    | 0, e => e
    | n+1, e =>
      let e := e.consumeMData
      match e with
      | .letE _ _ value body _ => head n (body.instantiate1 value)
      | _ =>
        match e.getAppFn.consumeMData with
        | .letE _ _ value body _ => head n (Lean.mkAppN (body.instantiate1 value) e.getAppArgs)
        | .lam .. =>
          let next := e.headBeta
          if Lean.Expr.equal next e then e else head n next
        | _ => e
  let next := head 64 action
  if !Lean.Expr.equal action next then
    let .app (.app (.app front _) _) _ := target | Lean.throwError "missing triple arguments"
    Lean.Elab.Tactic.replaceMainGoal [← goal.replaceTargetDefEq (Lean.mkApp3 front next pre args.back!)]
    return
  if (← Lean.Meta.matchMatcherApp? action).isSome then
    Lean.Elab.Tactic.replaceMainGoal (← Lean.Meta.Split.splitMatch goal action)
    return
  Lean.throwError "unhandled runner action"

theorem executeTraceLogged_nodup_wp
    (calls : ∀ call, Evolves (syscallLogged call))
    (trace : Trace) (placeholders : Bool) :
    ⦃fun h => ⌜h = []⌝⦄ executeTraceLogged trace placeholders
    ⦃⇓? _ h => ⌜h.Nodup⌝⦄ := by
  have syscall_spec (index : Nat) (w : World) (call : Syscall) :=
    runAtLogged_inv_wp (calls call) index w
  have ambient : SameView (fun w : World => snapshot w.wg) (skipAmbient : Leanux.M Unit) := by
    intro initial
    exact productAmbient_spec AmbientM.skipAmbient (fun w => snapshot w.wg = initial)
      (fun _ _ hp => hp)
  have ambient_spec (index : Nat) (w : World) :=
    ordinary_runAt_inv_wp
      (SameView.ordinary ambient) index w
  have routing (α : Type) (a : Net.M α) :
      SameView (fun w : World => snapshot w.wg) (liftM a : Leanux.M α) := by
    apply sameView_liftWG (fun w => snapshot w.wg) snapshot (liftRouting a)
    · intro initial
      exact hoare_liftRouting a (fun g => snapshot g = initial) (fun _ _ hp => hp)
    · intro w g ambient hg
      exact hg
  have boot : SameView (fun w : World => snapshot w.wg) (show Leanux.M Unit from do
      Net.Fib.bootTables
      if trace.foreign then Net.Fib.inCreatorNs Net.Fib.bootTables) := by
    apply SameView.bind (routing _ _)
    intro _
    split
    · exact routing _ _
    · exact SameView.pure _ _
  have boot_run (w : World) (x : Unit) (v : World)
      (hr : (show Leanux.M Unit from do
        Net.Fib.bootTables
        if trace.foreign then Net.Fib.inCreatorNs Net.Fib.bootTables).run w = .ok (x, v)) :
      snapshot v.wg = snapshot w.wg :=
    (Lifetimes.ProjectedAction.iff_run _ _ _).mp boot w x v hr

  let runnerInv : World → Assertion (.arg History (.except (Nat × Stop) .pure)) :=
    fun w h => ⌜Inv (snapshot w.wg) h⌝
  unfold executeTraceLogged
  repeat' first
    | (lifetime_runner_head runAtLogged;
        apply Triple.entails_wp_of_pre_post (syscall_spec _ _ _))
    | (lifetime_runner_head liftM;
        apply Triple.entails_wp_of_pre_post (ambient_spec _ _))
    | lifetime_runner_step runnerInv

  all_goals try
    solve
    | simp only [WP.monadLift_StateT, WP.throw_Except]
      intro history hi
      trivial
  all_goals try dsimp only [runnerInv] at *
  all_goals try exact .rfl
  all_goals try exact ⟨fun _ => .rfl, .rfl⟩
  all_goals try (solve | intros; assumption)
  all_goals try (solve | intro history hi; exact Inv.nodup hi)
  all_goals try
    solve
    | intro history hh
      change history = [] at hh
      subst history
      change Inv (snapshot (Runner.initialWG trace.net trace.bare)) []
      rw [initial_snapshot]
      exact inv_empty 0
  all_goals try
    solve
    | intro history hh
      change history = [] at hh
      subst history
      have hb := boot_run _ _ _ (by assumption)
      change Inv _ []
      rw [hb]
      change Inv (snapshot (Runner.initialWG trace.net trace.bare)) []
      rw [initial_snapshot]
      exact inv_empty 0

/-- Successful runner histories have no repeated event once the concrete
syscall observer contracts are supplied. This is an intermediate composition
lemma; the final S1 theorem discharges its caller premise. -/
theorem executeTraceLogged_nodup_of_calls
    (calls : ∀ call, Evolves (syscallLogged call))
    (trace : Trace) (placeholders : Bool) (json : Json) (history : History)
    (hr : (executeTraceLogged trace placeholders).run [] = .ok (json, history)) :
    history.Nodup :=
  (stateExceptHoare_iff_triple _ _ _).mpr
    (executeTraceLogged_nodup_wp calls trace placeholders) [] json history rfl hr

end Leanux.Proofs.WG.Keypairs.RunnerProof
