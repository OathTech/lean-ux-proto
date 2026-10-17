import Leanux.Proofs.WG.Configuration.RunnerCompletion

/-! Initialized routing agreement for the actual returned Runner World.
Address shape is required for both failed completion histories and normal
routing agreement, and is derived from the public parser. No earlier executed
lookup or packet-identity authorization follows from this endpoint theorem. -/
namespace Leanux.Proofs.WG.Configuration
open Lean Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged Leanux.Proofs.Framing
open Leanux.Proofs.WG.AllowedIps Std.Do
set_option maxHeartbeats 2000000
set_option pp.structureInstances false

private theorem routingRunnerTriple_ite {m : Type u → Type v} {ps : PostShape.{u}} [WP m ps]
    {α : Type u} {P : Assertion ps} {Q : PostCond α ps} (c : Prop) [Decidable c]
    (a b : m α) (ha : c → Triple a P Q) (hb : ¬c → Triple b P Q) :
    Triple (if c then a else b) P Q := by
  by_cases h : c
  · simpa only [h, ↓reduceIte] using ha h
  · simpa only [h, ↓reduceIte] using hb h

private theorem routingRunnerTriple_dite {m : Type u → Type v} {ps : PostShape.{u}} [WP m ps]
    {α : Type u} {P : Assertion ps} {Q : PostCond α ps} (c : Prop) [Decidable c]
    (a : c → m α) (b : ¬c → m α)
    (ha : ∀ h, Triple (a h) P Q) (hb : ∀ h, Triple (b h) P Q) :
    Triple (if h : c then a h else b h) P Q := by
  by_cases h : c
  · simpa only [h, ↓reduceDIte] using ha h
  · simpa only [h, ↓reduceDIte] using hb h

private theorem routing_runner_throw_bind {Event α β : Type} (e : Nat × Stop)
    (f : α → PrefixOuter Event β) :
    ((throw e : PrefixOuter Event α) >>= f) = throw e := rfl

/-- Select only the actual returned World in a runner accumulator. Other
results retain the current history assertion. -/
private def routingRunnerWorldAssertion (w : World) : Assertion
    (.except (Nat × Stop) (.arg (List RoutingCompletion) .pure)) :=
  fun h => ⌜GlobalCompletionState ([], []) h w.wg⌝

private def routingRunnerResultAssertion (type pre : Lean.Expr) : Lean.MetaM Lean.Expr := do
  Lean.Meta.withLocalDeclD `out type fun out => do
    let world? ←
      if ← Lean.Meta.isDefEq type (Lean.mkConst ``World) then pure (some out)
      else if type.isAppOf ``Prod then
        let args := type.getAppArgs
        if ← Lean.Meta.isDefEq args[0]! (Lean.mkConst ``World) then
          pure (some (Lean.mkProj ``Prod 0 out))
        else if ← Lean.Meta.isDefEq args[1]! (Lean.mkConst ``World) then
          pure (some (Lean.mkProj ``Prod 1 out))
        else pure none
      else pure none
    let assertion ← match world? with
      | some w => Lean.Meta.mkAppM ``routingRunnerWorldAssertion #[w]
      | none => pure pre
    Lean.Meta.mkLambdaFVars #[out] assertion

elab "routing_runner_wp_head " name:ident : tactic => do
  let ty := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless ty.isAppOf ``Triple && ty.getAppArgs.size ≥ 3 do Lean.throwError "not a triple"
  let args := ty.getAppArgs
  let action := args[args.size - 3]!.consumeMData
  let .const actual _ := action.getAppFn | Lean.throwError "not a constant action"
  let expected := name.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    Lean.throwError "different action"

elab "routing_runner_wp_call " name:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Triple && target.getAppArgs.size ≥ 3 do Lean.throwError "not a triple"
  let args := target.getAppArgs
  let action := args[args.size - 3]!.consumeMData
  unless action.isAppOf ``runAtPrefix && action.getAppArgs.size > 0 do Lean.throwError "not an indexed call"
  let .const actual _ := action.getAppArgs.back!.consumeMData.getAppFn
    | Lean.throwError "not a named observer"
  let expected := name.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    Lean.throwError "different indexed observer"

elab "routing_runner_wp_reduce" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Triple do Lean.throwError "not a triple"
  let .app (.app (.app front action) pre) post := target | Lean.throwError "missing action"
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
  let mut next := head 64 action
  if (← Lean.Meta.matchMatcherApp? next).isSome then
    if let .reduced reduced ← Lean.Meta.reduceMatcher? next then next := reduced
  if Lean.Expr.equal action next then Lean.throwError "head unchanged"
  Lean.Elab.Tactic.replaceMainGoal [← goal.replaceTargetDefEq (Lean.mkApp3 front next pre post)]

elab "routing_runner_wp_match" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Triple && target.getAppArgs.size ≥ 3 do Lean.throwError "not a triple"
  let args := target.getAppArgs
  let action := args[args.size - 3]!.consumeMData
  unless (← Lean.Meta.matchMatcherApp? action).isSome do Lean.throwError "not a head matcher"
  Lean.Elab.Tactic.replaceMainGoal (← Lean.Meta.Split.splitMatch goal action)

elab "routing_runner_wp_throw_bind" : tactic => Lean.Elab.Tactic.withMainContext do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Triple do Lean.throwError "not a triple"
  let args := target.getAppArgs
  let action := args[args.size - 3]!.consumeMData
  unless action.isAppOf ``Bind.bind do Lean.throwError "not a bind"
  let aa := action.getAppArgs
  let .const name _ := aa[aa.size - 2]!.consumeMData.getAppFn
    | Lean.throwError "not a throw"
  unless name.toString.endsWith ".throw" do Lean.throwError "not a throw"
  Lean.Elab.Tactic.evalTactic (← `(tactic| rw [routing_runner_throw_bind]))

elab "routing_runner_wp_bind" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Triple do Lean.throwError "not a triple"
  let args := target.getAppArgs
  let action := args[args.size - 3]!.consumeMData
  unless action.isAppOf ``Bind.bind do Lean.throwError "not a bind"
  let aa := action.getAppArgs
  let x := aa[aa.size - 2]!
  let type ← Lean.Meta.inferType x
  let result := type.getAppArgs.back!
  let q ← routingRunnerResultAssertion result args[args.size - 2]!
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

elab "routing_runner_wp_array" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Triple do Lean.throwError "not a triple"
  let args := target.getAppArgs
  let action := args[args.size - 3]!.consumeMData
  unless action.isAppOf ``ForIn.forIn do Lean.throwError "not forIn"
  let aa := action.getAppArgs
  let init := aa[aa.size - 2]!
  let result ← Lean.Meta.inferType init
  let q ← routingRunnerResultAssertion result args[args.size - 2]!
  let qsyntax ← Lean.PrettyPrinter.delab q
  let qtysyntax ← Lean.PrettyPrinter.delab (← Lean.Meta.inferType q)
  let qsyntax ← `(term| ($qsyntax : $qtysyntax))
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

theorem toSyscall_shape (results : Array Int) (ends : Array (Option (Nat × Nat)))
    (index : Nat) (op : Operation) (shape : OperationAddressShape op) :
    SyscallAddressShape (toSyscall results ends index op) := by
  cases op <;> simp only [toSyscall, SyscallAddressShape, OperationAddressShape] at shape ⊢
  exact shape

private theorem global_kernel {h : List RoutingCompletion} {w v : World}
    (hi : GlobalCompletionState initial h w.wg) (hk : productStoreView v = productStoreView w) :
    GlobalCompletionState initial h v.wg := by
  have hd : v.wg.dev = w.wg.dev := congrArg (fun store : ProductStore43 => store.2.2.2.dev) hk
  simpa only [GlobalCompletionState, routingView, hd] using hi

theorem runAtCompletion_wp {g : PrefixM RoutingCompletion α}
    (hg : PrefixPreserves (fun h (w : World) => GlobalCompletionState initial h w.wg) (CompletionSafe initial) g)
    (index : Nat) (w : World) :
    ⦃fun h => ⌜GlobalCompletionState initial h w.wg⌝⦄ runAtPrefix index w g
    ⦃post⟨fun out h => ⌜GlobalCompletionState initial h out.2.wg⌝,
      fun _ h => ⌜CompletionSafe initial h⌝⟩⦄ :=
  runAtPrefix_wp (show PrefixEnsures (fun h (w : World) => GlobalCompletionState initial h w.wg)
    (CompletionSafe initial) g (fun _ h (w : World) => GlobalCompletionState initial h w.wg) from hg) index w

private theorem shape_cursor (trace : Trace) (shape : TraceAddressShape trace)
    (pref : List Operation) (cur : Operation) (suff : List Operation)
    (h : trace.ops.toList = pref ++ cur :: suff) : OperationAddressShape cur :=
  shape cur (by rw [← Array.mem_toList_iff, h]; simp)

/-- The source-shaped post-initialization body preserves the actual accumulator
World. Array cursor membership supplies the shape of each executed operation. -/
theorem runnerTailObserved_wp (trace : Trace) (shape : TraceAddressShape trace) (w : World) :
    ⦃fun h => ⌜GlobalCompletionState ([], []) h w.wg⌝⦄ runnerTailObserved trace w
    ⦃post⟨fun out h => ⌜GlobalCompletionState ([], []) h out.2.wg⌝,
      fun _ h => ⌜CompletionSafe ([], []) h⌝⟩⦄ := by
  have syscall_spec (index : Nat) (w : World) (results : Array Int)
      (ends : Array (Option (Nat × Nat))) (op : Operation) (hs : OperationAddressShape op) :=
    runAtCompletion_wp (syscallObserved_global ([], []) _ (toSyscall_shape results ends index op hs)) index w
  have ambient_spec (index : Nat) (w : World) :=
    runAtCompletion_wp (global_completion_same World.wg ([], []) (skipAmbient : Leanux.M Unit)
      (by intro initial; exact productAmbient_spec _ _ (fun _ _ hi => hi))) index w
  delta runnerTailObserved
  repeat' first
    | (routing_runner_wp_call syscallObserved; apply Triple.entails_wp_of_pre_post (syscall_spec _ _ _ _ _ ?_))
    | (routing_runner_wp_call liftPrefix; apply Triple.entails_wp_of_pre_post (ambient_spec _ _))
    | (routing_runner_wp_head Pure.pure; apply Triple.pure
        (m := PrefixOuter RoutingCompletion) (ps := .except (Nat × Stop) (.arg (List RoutingCompletion) .pure)))
    | (routing_runner_wp_head throw; apply Triple.entails_wp_of_pre
        (Spec.throw_ExceptT (m := StateM (List RoutingCompletion)) (ps := .arg (List RoutingCompletion) .pure)))
    | routing_runner_wp_throw_bind
    | routing_runner_wp_bind
    | routing_runner_wp_array
    | routing_runner_wp_reduce
    | (routing_runner_wp_head ite; apply routingRunnerTriple_ite)
    | (routing_runner_wp_head dite; apply routingRunnerTriple_dite)
    | maintenance_intro
    | routing_runner_wp_match
  all_goals try dsimp only [routingRunnerWorldAssertion] at *
  all_goals try exact .rfl
  all_goals try exact ⟨fun _ => .rfl, .rfl⟩
  all_goals try (solve | intros; assumption)
  all_goals try (solve | intro history hi; exact global_kernel hi rfl)
  all_goals try (solve | intro history hi; exact hi.1)
  all_goals try exact shape_cursor trace shape _ _ _ (by assumption)

/-- Successful initialization supplies the actual routing state. Component
prefill is disjoint by type; routing boot preserves the original WG store.
Initialization failure retains the empty safe journal and no returned World. -/
theorem executeTraceObserved_wp (trace : Trace) (shape : TraceAddressShape trace)
    (placeholders : Bool) :
    ⦃fun h => ⌜h = []⌝⦄ executeTraceObserved trace placeholders
    ⦃post⟨fun out h => ⌜GlobalCompletionState ([], []) h out.2.wg⌝,
      fun _ h => ⌜CompletionSafe ([], []) h⌝⟩⦄ := by
  have tail_spec (w : World) := runnerTailObserved_wp trace shape w
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
    ((Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run _ _ _).mp (boot_store trace.foreign) w x v hr).trans hi
  delta executeTraceObserved
  by_cases hp : trace.seccompPrefill > 0
  all_goals simp only [hp, ↓reduceIte]
  all_goals cases Env.seccompPrefill trace.seccompPrefill ({} : SeccompWorld) (initialTasks trace.rlimit trace.foreign trace.stepped trace.seccompChild)
  all_goals repeat' first
    | (routing_runner_wp_head runnerTailObserved; apply Triple.entails_wp_of_pre_post (tail_spec _))
    | (routing_runner_wp_head Pure.pure; apply Triple.pure
        (m := PrefixOuter RoutingCompletion) (ps := .except (Nat × Stop) (.arg (List RoutingCompletion) .pure)))
    | (routing_runner_wp_head throw; apply Triple.entails_wp_of_pre
        (Spec.throw_ExceptT (m := StateM (List RoutingCompletion)) (ps := .arg (List RoutingCompletion) .pure)))
    | routing_runner_wp_throw_bind
    | routing_runner_wp_bind
    | routing_runner_wp_reduce
    | (routing_runner_wp_head ite; apply routingRunnerTriple_ite)
    | (routing_runner_wp_head dite; apply routingRunnerTriple_dite)
    | maintenance_intro
    | routing_runner_wp_match
  all_goals try dsimp only [routingRunnerWorldAssertion] at *
  all_goals try exact .rfl
  all_goals try exact ⟨fun _ => .rfl, .rfl⟩
  all_goals try (solve | intros; assumption)
  all_goals try (solve | intro history hi; exact hi.1)
  all_goals try
    solve
    | intro history hh
      change history = [] at hh
      subst history
      exact CompletionSafe.nil
  all_goals intro history hh
  all_goals change history = [] at hh
  all_goals subst history
  all_goals change GlobalCompletionState ([], []) [] _
  all_goals first
    | exact global_initial trace
        { ambient := { env := harnessEnv, timing := Env.timing },
          tasks := initialTasks 0, fs := initialFS, wg := _ } rfl
    | exact global_initial trace _ (boot_initial _ _ _ (by assumption) rfl)

/-- The actual initialized result retains valid completions on every outcome;
only a normal result supplies the final accumulator World. -/
theorem executeTraceObserved_routing (trace : Trace) (shape : TraceAddressShape trace)
    (placeholders : Bool) :
    CompletionSafe ([], []) (runPrefixOuter (executeTraceObserved trace placeholders) []).2 ∧
    ∀ out, (runPrefixOuter (executeTraceObserved trace placeholders) []).1 = .ok out →
      GlobalCompletionState ([], []) (runPrefixOuter (executeTraceObserved trace placeholders) []).2 out.2.wg := by
  have hs := (prefixOuter_wp_iff _ _ _ _).mp
    (executeTraceObserved_wp trace shape placeholders) [] rfl
  cases hr : runPrefixOuter (executeTraceObserved trace placeholders) [] with
  | mk result hist =>
    cases result with
    | error e =>
      simp only [hr] at hs ⊢
      exact ⟨hs, fun _ he => by cases he⟩
    | ok out =>
      simp only [hr] at hs ⊢
      exact ⟨hs.1, fun _ he => by cases he; exact hs⟩

theorem parsed_executeTraceObserved_routing (json : Json) (trace : Trace)
    (parsed : Runner.parseTrace json = .ok trace) (placeholders : Bool) :
    CompletionSafe ([], []) (runPrefixOuter (executeTraceObserved trace placeholders) []).2 ∧
    ∀ out, (runPrefixOuter (executeTraceObserved trace placeholders) []).1 = .ok out →
      GlobalCompletionState ([], []) (runPrefixOuter (executeTraceObserved trace placeholders) []).2 out.2.wg :=
  executeTraceObserved_routing trace (parseTrace_shape json trace parsed) placeholders

end Leanux.Proofs.WG.Configuration
