import Leanux.Proofs.WG.Lifetimes.RunnerAudit
import Leanux.Proofs.WG.Lifetimes.AllocationInitial

/-! Initialized allocation-identity access safety for every typed Runner trace.
Successful and failed executions retain safe committed observations and valid
saved consistency-filter entries; copied trial histories remain separate. -/
namespace Leanux.Proofs.WG.Lifetimes
open Lean Leanux Leanux.Runner Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
set_option maxHeartbeats 2000000
set_option pp.structureInstances false

private theorem runnerTriple_ite {m : Type u → Type v} {ps : PostShape.{u}} [WP m ps]
    {α : Type u} {P : Assertion ps} {Q : PostCond α ps} (c : Prop) [Decidable c]
    (a b : m α) (ha : c → Triple a P Q) (hb : ¬c → Triple b P Q) :
    Triple (if c then a else b) P Q := by
  by_cases h : c
  · simpa only [h, ↓reduceIte] using ha h
  · simpa only [h, ↓reduceIte] using hb h

private theorem runnerTriple_dite {m : Type u → Type v} {ps : PostShape.{u}} [WP m ps]
    {α : Type u} {P : Assertion ps} {Q : PostCond α ps} (c : Prop) [Decidable c]
    (a : c → m α) (b : ¬c → m α)
    (ha : ∀ h, Triple (a h) P Q) (hb : ∀ h, Triple (b h) P Q) :
    Triple (if h : c then a h else b h) P Q := by
  by_cases h : c
  · simpa only [h, ↓reduceDIte] using ha h
  · simpa only [h, ↓reduceDIte] using hb h

private theorem runner_throw_bind {Event α β : Type} (e : Nat × Stop)
    (f : α → PrefixOuter Event β) :
    ((throw e : PrefixOuter Event α) >>= f) = throw e := rfl

theorem runAtAudit_wp {g : AuditM α} (hg : PrefixPreserves AuditInv AuditSafe g)
    (index : Nat) (w : World) :
    ⦃fun h => ⌜AuditInv h w⌝⦄ runAtPrefix index w g
    ⦃post⟨fun out h => ⌜AuditInv h out.2⌝, fun _ h => ⌜AuditSafe h⌝⟩⦄ :=
  runAtPrefix_wp (show PrefixEnsures AuditInv AuditSafe g (fun _ => AuditInv) from hg) index w


/-- Select only the actual returned World in a runner accumulator. Other
results retain the current history assertion. -/
private def runnerWorldAssertion (w : World) : Assertion
    (.except (Nat × Stop) (.arg (List AuditEvent) .pure)) :=
  fun h => ⌜AuditInv h w⌝

private def runnerResultAssertion (type pre : Lean.Expr) : Lean.MetaM Lean.Expr := do
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
      | some w => Lean.Meta.mkAppM ``runnerWorldAssertion #[w]
      | none => pure pre
    Lean.Meta.mkLambdaFVars #[out] assertion

elab "runner_wp_head " name:ident : tactic => do
  let ty := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless ty.isAppOf ``Triple && ty.getAppArgs.size ≥ 3 do Lean.throwError "not a triple"
  let args := ty.getAppArgs
  let action := args[args.size - 3]!.consumeMData
  let .const actual _ := action.getAppFn | Lean.throwError "not a constant action"
  let expected := name.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    Lean.throwError "different action"

elab "runner_wp_call " name:ident : tactic => do
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

elab "runner_wp_reduce" : tactic => Lean.Elab.Tactic.withMainContext do
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

elab "runner_wp_match" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Triple && target.getAppArgs.size ≥ 3 do Lean.throwError "not a triple"
  let args := target.getAppArgs
  let action := args[args.size - 3]!.consumeMData
  unless (← Lean.Meta.matchMatcherApp? action).isSome do Lean.throwError "not a head matcher"
  Lean.Elab.Tactic.replaceMainGoal (← Lean.Meta.Split.splitMatch goal action)

elab "runner_wp_throw_bind" : tactic => Lean.Elab.Tactic.withMainContext do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Triple do Lean.throwError "not a triple"
  let args := target.getAppArgs
  let action := args[args.size - 3]!.consumeMData
  unless action.isAppOf ``Bind.bind do Lean.throwError "not a bind"
  let aa := action.getAppArgs
  let .const name _ := aa[aa.size - 2]!.consumeMData.getAppFn
    | Lean.throwError "not a throw"
  unless name.toString.endsWith ".throw" do Lean.throwError "not a throw"
  Lean.Elab.Tactic.evalTactic (← `(tactic| rw [runner_throw_bind]))

elab "runner_wp_bind" : tactic => Lean.Elab.Tactic.withMainContext do
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
  let q ← runnerResultAssertion result args[args.size - 2]!
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

elab "runner_wp_array" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Triple do Lean.throwError "not a triple"
  let args := target.getAppArgs
  let action := args[args.size - 3]!.consumeMData
  unless action.isAppOf ``ForIn.forIn do Lean.throwError "not forIn"
  let aa := action.getAppArgs
  let init := aa[aa.size - 2]!
  let result ← Lean.Meta.inferType init
  let q ← runnerResultAssertion result args[args.size - 2]!
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

private theorem runnerAuditTail_safe_wp (trace : Trace) (w : World) :
    ⦃fun h => ⌜AuditInv h w⌝⦄ runnerAuditTail trace w
    ⦃post⟨fun _ h => ⌜AuditSafe h⌝, fun _ h => ⌜AuditSafe h⌝⟩⦄ := by
  have syscall_spec (index : Nat) (w : World) (call : Syscall) :=
    runAtAudit_wp (syscallAudit_preserves call) index w
  have ambient_spec (index : Nat) (w : World) :=
    runAtAudit_wp (auditLift_store skipAmbient (by
      intro initial
      exact productAmbient_spec _ _ (fun _ _ hi => hi))) index w
  unfold runnerAuditTail
  repeat' first
    | (runner_wp_call syscallAudit; apply Triple.entails_wp_of_pre_post (syscall_spec _ _ _))
    | (runner_wp_call liftPrefix; apply Triple.entails_wp_of_pre_post (ambient_spec _ _))
    | (runner_wp_head Pure.pure; apply Triple.pure
        (m := PrefixOuter AuditEvent) (ps := .except (Nat × Stop) (.arg (List AuditEvent) .pure)))
    | (runner_wp_head throw; apply Triple.entails_wp_of_pre
        (Spec.throw_ExceptT (m := StateM (List AuditEvent)) (ps := .arg (List AuditEvent) .pure)))
    | runner_wp_throw_bind
    | runner_wp_bind
    | runner_wp_array
    | runner_wp_reduce
    | (runner_wp_head ite; apply runnerTriple_ite)
    | (runner_wp_head dite; apply runnerTriple_dite)
    | maintenance_intro
    | runner_wp_match
  all_goals try dsimp only [runnerWorldAssertion] at *
  all_goals try exact .rfl
  all_goals try exact ⟨fun _ => .rfl, .rfl⟩
  all_goals try (solve | intros; assumption)
  all_goals try (solve | intro history hi; exact AuditInv.store hi rfl)
  all_goals try (solve | intro history hi; exact AuditInv.safe hi)


/-- The initialization and every concrete syscall discharge the state premise;
both WP branches retain safety, including failed prefill and end guards. -/
theorem executeTraceAudit_safe_wp (trace : Trace) (placeholders : Bool) :
    ⦃fun h => ⌜h = []⌝⦄ executeTraceAudit trace placeholders
    ⦃post⟨fun _ h => ⌜AuditSafe h⌝, fun _ h => ⌜AuditSafe h⌝⟩⦄ := by
  have tail_spec (w : World) := runnerAuditTail_safe_wp trace w
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
  unfold executeTraceAudit
  by_cases hp : trace.seccompPrefill > 0
  all_goals simp only [hp, ↓reduceIte]
  all_goals cases Env.seccompPrefill trace.seccompPrefill ({} : SeccompWorld) (initialTasks trace.rlimit trace.foreign trace.stepped trace.seccompChild)
  all_goals repeat' first
    | (runner_wp_head runnerAuditTail; apply Triple.entails_wp_of_pre_post (tail_spec _))
    | (runner_wp_head Pure.pure; apply Triple.pure
        (m := PrefixOuter AuditEvent) (ps := .except (Nat × Stop) (.arg (List AuditEvent) .pure)))
    | (runner_wp_head throw; apply Triple.entails_wp_of_pre
        (Spec.throw_ExceptT (m := StateM (List AuditEvent)) (ps := .arg (List AuditEvent) .pure)))
    | runner_wp_throw_bind
    | runner_wp_bind
    | runner_wp_array
    | runner_wp_reduce
    | (runner_wp_head ite; apply runnerTriple_ite)
    | (runner_wp_head dite; apply runnerTriple_dite)
    | maintenance_intro
    | runner_wp_match
  all_goals try dsimp only [runnerWorldAssertion] at *
  all_goals try exact .rfl
  all_goals try exact ⟨fun _ => .rfl, .rfl⟩
  all_goals try (solve | intros; assumption)
  all_goals try (solve | intro history hi; exact AuditInv.store hi rfl)
  all_goals try (solve | intro history hi; exact AuditInv.safe hi)
  all_goals
    intro history hi
    change history = [] at hi
    subst history
    first
    | change AuditSafe []
      exact ⟨⟨AccessEvent.safe_nil, AccessEvent.safe_nil, AccessEvent.safe_nil⟩,
        by simp [AllProbeValid, probeEntries]⟩
    | apply audit_initial
      apply allocation_initial trace.net trace.bare
      first
      | rfl
      | rename_i hrun
        have hb := boot_initial _ _ _ hrun (by rfl)
        exact hb

/-- Safety is unconditional in the original result: Stops preserve their reached
committed history and saved filter-entry validity just as successful JSON does. -/
theorem executeTraceAudit_safe (trace : Trace) (placeholders : Bool) :
    AuditSafe (runPrefixOuter (executeTraceAudit trace placeholders) []).2 := by
  have hs := (prefixOuter_wp_iff _ _ _ _).mp
    (executeTraceAudit_safe_wp trace placeholders) [] rfl
  cases hr : runPrefixOuter (executeTraceAudit trace placeholders) [] with
  | mk result hist => cases result <;> simpa only [hr] using hs

/-- Every reached saved filter entry is valid from initialized execution. Exact
filter order and early failure identify the evaluated prefix; certifying all
candidates does not assert that later candidates were evaluated. -/
theorem executeTraceAudit_trials (trace : Trace) (placeholders : Bool) :
    ∀ p ∈ probeEntries (runPrefixOuter (executeTraceAudit trace placeholders) []).2,
      AllocationInv p.history p.world.wg ∧
      (p.world.ambient.suspended.filterM Env.Activation.consistent).run p.world =
        (p.world.ambient.suspended.filterM (fun a => activationTrialDecision a p.world p.history)).map
          (fun ys => (ys, p.world)) ∧
      ∀ a ∈ p.world.ambient.suspended,
        LifetimeEvent.Safe (runPrefix (activationRunPrefix a) p.world p.history).2 := by
  intro p hp
  exact savedProbe_trials (executeTraceAudit_safe trace placeholders).2 hp

end Leanux.Proofs.WG.Lifetimes
