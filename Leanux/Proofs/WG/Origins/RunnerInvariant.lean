import Leanux.Proofs.WG.Origins.SupportRunner

/-! Generic invariant composition over the existing initialized runner. The
syscall observer remains arbitrary, and indexed Stops keep the reached journal.
Initialization and administrative updates use only the seven WG store fields. -/
namespace Leanux.Proofs.WG.RunnerInvariant
open Lean Leanux Leanux.Runner Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Origins.HistorySupport Std.Do

private def worldAssertion {E : Type} (I : List E → World → Prop) (w : World) :
    Assertion (.except (Nat × Stop) (.arg (List E) .pure)) :=
  fun h => ⌜I h w⌝

private def resultAssertion (invariant type pre : Lean.Expr) : Lean.MetaM Lean.Expr := do
  Lean.Meta.withLocalDeclD `out type fun out => do
    let world? ←
      if ← Lean.Meta.isDefEq type (Lean.mkConst ``World) then pure (some out)
      else if type.isAppOf ``Prod && type.getAppArgs.size == 2 then
        let args := type.getAppArgs
        if ← Lean.Meta.isDefEq args[0]! (Lean.mkConst ``World) then
          pure (some (Lean.mkProj ``Prod 0 out))
        else if ← Lean.Meta.isDefEq args[1]! (Lean.mkConst ``World) then
          pure (some (Lean.mkProj ``Prod 1 out))
        else pure none
      else pure none
    let assertion ← match world? with
      | some w => Lean.Meta.mkAppM ``worldAssertion #[invariant, w]
      | none => pure pre
    Lean.Meta.mkLambdaFVars #[out] assertion

elab "runner_invariant_bind " invariant:ident : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Triple && target.getAppArgs.size ≥ 5 do Lean.throwError "not a triple"
  let args := target.getAppArgs
  let action := args[args.size - 3]!.consumeMData
  unless action.isAppOf ``Bind.bind && action.getAppArgs.size ≥ 2 do Lean.throwError "not a bind"
  let aa := action.getAppArgs
  let x := aa[aa.size - 2]!
  let type ← Lean.Meta.inferType x
  unless !type.getAppArgs.isEmpty do Lean.throwError "action has no result type"
  let result := type.getAppArgs.back!
  let invariant ← Lean.Elab.Term.elabTerm invariant none
  let q ← resultAssertion invariant result args[args.size - 2]!
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
      | "P" => pure args[args.size - 2]!
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

elab "runner_invariant_array " invariant:ident : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Triple && target.getAppArgs.size ≥ 5 do Lean.throwError "not a triple"
  let args := target.getAppArgs
  let action := args[args.size - 3]!.consumeMData
  unless action.isAppOf ``ForIn.forIn && action.getAppArgs.size ≥ 2 do Lean.throwError "not forIn"
  let aa := action.getAppArgs
  let init := aa[aa.size - 2]!
  let result ← Lean.Meta.inferType init
  let invariant ← Lean.Elab.Term.elabTerm invariant none
  let q ← resultAssertion invariant result args[args.size - 2]!
  let qterm ← Lean.PrettyPrinter.delab q
  let qtype ← Lean.PrettyPrinter.delab (← Lean.Meta.inferType q)
  let qsyntax ← `(term| ($qterm : $qtype))
  let err ← Lean.Meta.whnf (Lean.mkProj ``Prod 1 args.back!)
  let esyntax ← Lean.PrettyPrinter.delab err
  let psyntax ← Lean.PrettyPrinter.delab args[1]!
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    apply Triple.entails_wp_of_pre_post (ps := $psyntax) (Q' := ($qsyntax, $esyntax))))
  let rest := (← Lean.Elab.Tactic.getGoals).tail
  Lean.Elab.Tactic.setGoals [(← Lean.Elab.Tactic.getMainGoal)]
  Lean.Elab.Tactic.evalTactic (← `(tactic| rw [← Array.forIn_toList]))
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply Spec.forIn_list_const_inv))
  Lean.Elab.Tactic.evalTactic (← `(tactic| intro hd acc))
  Lean.Elab.Tactic.setGoals ((← Lean.Elab.Tactic.getGoals) ++ rest)

open Lean Meta Elab Tactic in
elab "runner_invariant_callback " callback:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Triple && target.getAppArgs.size ≥ 3 do
    throwError "not a triple"
  let args := target.getAppArgs
  let action := args[args.size - 3]!.consumeMData
  unless action.isAppOf ``runAtPrefix && !action.getAppArgs.isEmpty do
    throwError "not an indexed prefix"
  let source := action.getAppArgs.back!.consumeMData
  let callback ← Term.elabTerm callback none
  unless source.getAppFn == callback.consumeMData do
    throwError "not the selected callback"

variable {E : Type}

/-- The literal runner tail preserves safe history for every syscall observer
with the supplied normal-state and failed-prefix contract. -/
theorem runnerTail_wp (I : List E → World → Prop) (S : List E → Prop)
    (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, wgStoreView v.wg = wgStoreView w.wg → I h w → I h v)
    (call : Syscall → PrefixM E Int)
    (calls : ∀ c, PrefixPreserves I S (call c)) (trace : Trace) (w : World) :
    ⦃fun h => ⌜I h w⌝⦄ RxHistory.runnerTail call trace w
    ⦃post⟨fun _ h => ⌜S h⌝, fun _ h => ⌜S h⌝⟩⦄ := by
  have syscall_spec (index : Nat) (w : World) (c : Syscall) :=
    runAtPrefix_wp (show PrefixEnsures I S (call c) (fun _ => I) from calls c) index w
  have ambient : PrefixPreserves I S (liftPrefix (skipAmbient : Leanux.M Unit)) := by
    apply viewLiftPrefix_preserves (fun w : World => wgStoreView w.wg) safe store
    intro initial
    exact productAmbient_spec _ (fun w => wgStoreView w.wg = initial) (fun _ _ hi => hi)
  have ambient_spec (index : Nat) (w : World) := runAtPrefix_wp ambient index w
  unfold RxHistory.runnerTail
  repeat' first
    | (runner_invariant_callback call; apply Triple.entails_wp_of_pre_post (syscall_spec _ _ _))
    | (support_runner_wp_call liftPrefix; apply Triple.entails_wp_of_pre_post (ambient_spec _ _))
    | (support_runner_wp_head Pure.pure; apply Triple.pure
        (m := PrefixOuter E) (ps := .except (Nat × Stop) (.arg (List E) .pure)))
    | (support_runner_wp_head throw; apply Triple.entails_wp_of_pre
        (Spec.throw_ExceptT (m := StateM (List E)) (ps := .arg (List E) .pure)))
    | support_runner_wp_throw_bind
    | runner_invariant_bind I
    | runner_invariant_array I
    | support_runner_wp_reduce
    | (support_runner_wp_head ite
       apply (pinned_const _private.Leanux.Proofs.WG.Origins.SupportRunner.«0».Leanux.Proofs.WG.Origins.HistorySupport.supportRunnerTriple_ite))
    | (support_runner_wp_head dite
       apply (pinned_const _private.Leanux.Proofs.WG.Origins.SupportRunner.«0».Leanux.Proofs.WG.Origins.HistorySupport.supportRunnerTriple_dite))
    | maintenance_intro
    | support_runner_wp_match
  all_goals try dsimp only [worldAssertion] at *
  all_goals try exact .rfl
  all_goals try exact ⟨fun _ => .rfl, .rfl⟩
  all_goals try (solve | intros; assumption)
  all_goals try (solve | intro history hi; apply store history _ _ ?_ hi; rfl)
  all_goals try (solve | intro history hi; exact safe history _ hi)

/-- The actual fixture establishes the invariant from the original seven-field
premise. Every normal or indexed-Stop outcome retains safe history. -/
theorem executeTraceWith_wp (I : List E → World → Prop) (S : List E → Prop)
    (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, wgStoreView v.wg = wgStoreView w.wg → I h w → I h v)
    (call : Syscall → PrefixM E Int)
    (calls : ∀ c, PrefixPreserves I S (call c)) (trace : Trace) (placeholders : Bool)
    (initial : ∀ w, wgStoreView w.wg = wgStoreView (initialWG trace.net trace.bare) → I [] w) :
    ⦃fun h => ⌜h = []⌝⦄ RxHistory.executeTraceWith call trace placeholders
    ⦃post⟨fun _ h => ⌜S h⌝, fun _ h => ⌜S h⌝⟩⦄ := by
  have tail_spec (w : World) := runnerTail_wp I S safe store call calls trace w
  have empty : S [] := safe []
    { ambient := { env := harnessEnv, timing := Env.timing },
      tasks := initialTasks trace.rlimit, fs := initialFS trace.net,
      wg := initialWG trace.net trace.bare } (initial _ rfl)
  have boot_store (foreign : Bool) : SameView (fun w => wgStoreView w.wg)
      (do Net.Fib.bootTables
          if foreign then Net.Fib.inCreatorNs Net.Fib.bootTables : Leanux.M Unit) := by
    apply SameView.bind
    · intro initial
      exact productRouting_spec _ (fun s => s.2.2.2 = initial)
    · intro _
      split
      · intro initial
        exact productRouting_spec _ (fun s => s.2.2.2 = initial)
      · exact SameView.pure _ _
  have boot_initial (w v : World) (x : Unit)
      (hr : (do Net.Fib.bootTables
                if trace.foreign then Net.Fib.inCreatorNs Net.Fib.bootTables : Leanux.M Unit).run w = .ok (x, v))
      (hi : wgStoreView w.wg = wgStoreView (initialWG trace.net trace.bare)) :
      wgStoreView v.wg = wgStoreView (initialWG trace.net trace.bare) :=
    ((ProjectedAction.iff_run _ _ _).mp (boot_store trace.foreign) w x v hr).trans hi
  unfold RxHistory.executeTraceWith
  by_cases hp : trace.seccompPrefill > 0
  all_goals simp only [hp, ↓reduceIte]
  all_goals cases Env.seccompPrefill trace.seccompPrefill ({} : SeccompWorld) (initialTasks trace.rlimit trace.foreign trace.stepped trace.seccompChild)
  all_goals repeat' first
    | (support_runner_wp_head RxHistory.runnerTail; apply Triple.entails_wp_of_pre_post (tail_spec _))
    | (support_runner_wp_head Pure.pure; apply Triple.pure
        (m := PrefixOuter E) (ps := .except (Nat × Stop) (.arg (List E) .pure)))
    | (support_runner_wp_head throw; apply Triple.entails_wp_of_pre
        (Spec.throw_ExceptT (m := StateM (List E)) (ps := .arg (List E) .pure)))
    | support_runner_wp_throw_bind
    | runner_invariant_bind I
    | runner_invariant_array I
    | support_runner_wp_reduce
    | (support_runner_wp_head ite
       apply (pinned_const _private.Leanux.Proofs.WG.Origins.SupportRunner.«0».Leanux.Proofs.WG.Origins.HistorySupport.supportRunnerTriple_ite))
    | (support_runner_wp_head dite
       apply (pinned_const _private.Leanux.Proofs.WG.Origins.SupportRunner.«0».Leanux.Proofs.WG.Origins.HistorySupport.supportRunnerTriple_dite))
    | maintenance_intro
    | support_runner_wp_match
  all_goals try dsimp only [worldAssertion] at *
  all_goals try exact .rfl
  all_goals try exact ⟨fun _ => .rfl, .rfl⟩
  all_goals try (solve | intros; assumption)
  all_goals try (solve | intro history hi; apply store history _ _ ?_ hi; rfl)
  all_goals try (solve | intro history hi; exact safe history _ hi)
  all_goals
    intro history hi
    change history = [] at hi
    subst history
    first
    | exact empty
    | apply initial
      first
      | rfl
      | rename_i hrun
        have hb := boot_initial _ _ _ hrun (by rfl)
        exact hb

/-- The original runner returns JSON or an indexed Stop without losing its
journal invariant. No successful termination or callback totality is assumed. -/
theorem executeTraceWith (I : List E → World → Prop) (S : List E → Prop)
    (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, wgStoreView v.wg = wgStoreView w.wg → I h w → I h v)
    (call : Syscall → PrefixM E Int)
    (calls : ∀ c, PrefixPreserves I S (call c)) (trace : Trace) (placeholders : Bool)
    (initial : ∀ w, wgStoreView w.wg = wgStoreView (initialWG trace.net trace.bare) → I [] w) :
    S (runPrefixOuter (RxHistory.executeTraceWith call trace placeholders) []).2 := by
  have checked := (prefixOuter_wp_iff _ _ _ _).mp
    (executeTraceWith_wp I S safe store call calls trace placeholders initial) [] rfl
  cases hr : runPrefixOuter (RxHistory.executeTraceWith call trace placeholders) [] with
  | mk result hist => cases result <;> simpa only [hr] using checked

end Leanux.Proofs.WG.RunnerInvariant
