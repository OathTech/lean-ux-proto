import Leanux.Proofs.WG.Origins.RunnerInvariant

/-! The same initialized runner invariant, with contracts required only for
syscalls produced by operations in the actual trace. Array cursor membership
supplies this premise without changing the callback or runner observer. -/
namespace Leanux.Proofs.WG.RunnerInvariant.Shaped
open Lean Leanux Leanux.Runner Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Origins.HistorySupport Std.Do

elab "shaped_runner_array " invariant:ident : tactic => Lean.Elab.Tactic.withMainContext do
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
  let q ← (pinned_const _private.Leanux.Proofs.WG.Origins.RunnerInvariant.«0».Leanux.Proofs.WG.RunnerInvariant.resultAssertion) invariant result args[args.size - 2]!
  let q ← Lean.Meta.deltaExpand q fun name =>
    name.toString.endsWith ".Leanux.Proofs.WG.RunnerInvariant.worldAssertion"
  let qterm ← Lean.PrettyPrinter.delab q
  let qtype ← Lean.PrettyPrinter.delab (← Lean.Meta.inferType q)
  let qsyntax ← `(term| ($qterm : $qtype))
  let err ← Lean.Meta.whnf (Lean.mkProj ``Prod 1 args.back!)
  let err ← Lean.Meta.deltaExpand err fun name =>
    name.toString.endsWith ".Leanux.Proofs.WG.RunnerInvariant.worldAssertion"
  let esyntax ← Lean.PrettyPrinter.delab err
  let psyntax ← Lean.PrettyPrinter.delab args[1]!
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    apply Triple.entails_wp_of_pre_post (ps := $psyntax) (Q' := ($qsyntax, $esyntax))))
  let rest := (← Lean.Elab.Tactic.getGoals).tail
  Lean.Elab.Tactic.setGoals [(← Lean.Elab.Tactic.getMainGoal)]
  Lean.Elab.Tactic.evalTactic (← `(tactic| rw [← Array.forIn_toList]))
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply Spec.forIn_list (ps := $psyntax) (fun p => $qsyntax p.2, $esyntax)))
  Lean.Elab.Tactic.evalTactic (← `(tactic| intro pref cur suff cursor acc))
  Lean.Elab.Tactic.setGoals ((← Lean.Elab.Tactic.getGoals) ++ rest)

private theorem member_cursor (trace : Trace) (pref : List Operation)
    (cur : Operation) (suff : List Operation)
    (h : trace.ops.toList = pref ++ cur :: suff) : cur ∈ trace.ops := by
  rw [← Array.mem_toList_iff,h]
  simp

variable {E : Type}

/-- The literal runner tail preserves safe history for every syscall observer
with the supplied normal-state and failed-prefix contract. -/
theorem runnerTail_wp (I : List E → World → Prop) (S : List E → Prop)
    (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, wgStoreView v.wg = wgStoreView w.wg → I h w → I h v)
    (accept : Syscall → Prop) (call : Syscall → PrefixM E Int)
    (calls : ∀ c, accept c → PrefixPreserves I S (call c)) (trace : Trace)
    (traceCalls : ∀ op, op ∈ trace.ops → ∀ results ends index, accept (toSyscall results ends index op)) (w : World) :
    ⦃fun h => ⌜I h w⌝⦄ RxHistory.runnerTail call trace w
    ⦃post⟨fun _ h => ⌜S h⌝, fun _ h => ⌜S h⌝⟩⦄ := by
  have syscall_spec (index : Nat) (w : World) (results : Array Int)
      (ends : Array (Option (Nat × Nat))) (op : Operation) (member : op ∈ trace.ops) :=
    runAtPrefix_wp (show PrefixEnsures I S (call (toSyscall results ends index op)) (fun _ => I)
      from calls _ (traceCalls op member results ends index)) index w
  have ambient : PrefixPreserves I S (liftPrefix (skipAmbient : Leanux.M Unit)) := by
    apply viewLiftPrefix_preserves (fun w : World => wgStoreView w.wg) safe store
    intro initial
    exact productAmbient_spec _ (fun w => wgStoreView w.wg = initial) (fun _ _ hi => hi)
  have ambient_spec (index : Nat) (w : World) := runAtPrefix_wp ambient index w
  unfold RxHistory.runnerTail
  repeat' first
    | (runner_invariant_callback call; apply Triple.entails_wp_of_pre_post (syscall_spec _ _ _ _ _ ?_))
    | (support_runner_wp_call liftPrefix; apply Triple.entails_wp_of_pre_post (ambient_spec _ _))
    | (support_runner_wp_head Pure.pure; apply Triple.pure
        (m := PrefixOuter E) (ps := .except (Nat × Stop) (.arg (List E) .pure)))
    | (support_runner_wp_head throw; apply Triple.entails_wp_of_pre
        (Spec.throw_ExceptT (m := StateM (List E)) (ps := .arg (List E) .pure)))
    | support_runner_wp_throw_bind
    | runner_invariant_bind I
    | shaped_runner_array I
    | support_runner_wp_reduce
    | (support_runner_wp_head ite
       apply (pinned_const _private.Leanux.Proofs.WG.Origins.SupportRunner.«0».Leanux.Proofs.WG.Origins.HistorySupport.supportRunnerTriple_ite))
    | (support_runner_wp_head dite
       apply (pinned_const _private.Leanux.Proofs.WG.Origins.SupportRunner.«0».Leanux.Proofs.WG.Origins.HistorySupport.supportRunnerTriple_dite))
    | maintenance_intro
    | support_runner_wp_match
  all_goals try dsimp only [(pinned_const _private.Leanux.Proofs.WG.Origins.RunnerInvariant.«0».Leanux.Proofs.WG.RunnerInvariant.worldAssertion)] at *
  all_goals try exact .rfl
  all_goals try exact ⟨fun _ => .rfl, .rfl⟩
  all_goals try (solve | intros; assumption)
  all_goals try (solve | intro history hi; apply store history _ _ ?_ hi; rfl)
  all_goals try (solve | intro history hi; exact safe history _ hi)
  all_goals try exact member_cursor trace _ _ _ (by assumption)
  all_goals shaped_runner_array I

/-- The actual fixture establishes the invariant from the original seven-field
premise. Every normal or indexed-Stop outcome retains safe history. -/
theorem executeTraceWith_wp (I : List E → World → Prop) (S : List E → Prop)
    (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, wgStoreView v.wg = wgStoreView w.wg → I h w → I h v)
    (accept : Syscall → Prop) (call : Syscall → PrefixM E Int)
    (calls : ∀ c, accept c → PrefixPreserves I S (call c)) (trace : Trace)
    (traceCalls : ∀ op, op ∈ trace.ops → ∀ results ends index, accept (toSyscall results ends index op)) (placeholders : Bool)
    (initial : ∀ w, wgStoreView w.wg = wgStoreView (initialWG trace.net trace.bare) → I [] w) :
    ⦃fun h => ⌜h = []⌝⦄ RxHistory.executeTraceWith call trace placeholders
    ⦃post⟨fun _ h => ⌜S h⌝, fun _ h => ⌜S h⌝⟩⦄ := by
  have tail_spec (w : World) := runnerTail_wp I S safe store accept call calls trace traceCalls w
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
    | shaped_runner_array I
    | support_runner_wp_reduce
    | (support_runner_wp_head ite
       apply (pinned_const _private.Leanux.Proofs.WG.Origins.SupportRunner.«0».Leanux.Proofs.WG.Origins.HistorySupport.supportRunnerTriple_ite))
    | (support_runner_wp_head dite
       apply (pinned_const _private.Leanux.Proofs.WG.Origins.SupportRunner.«0».Leanux.Proofs.WG.Origins.HistorySupport.supportRunnerTriple_dite))
    | maintenance_intro
    | support_runner_wp_match
  all_goals try dsimp only [(pinned_const _private.Leanux.Proofs.WG.Origins.RunnerInvariant.«0».Leanux.Proofs.WG.RunnerInvariant.worldAssertion)] at *
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
    (accept : Syscall → Prop) (call : Syscall → PrefixM E Int)
    (calls : ∀ c, accept c → PrefixPreserves I S (call c)) (trace : Trace)
    (traceCalls : ∀ op, op ∈ trace.ops → ∀ results ends index, accept (toSyscall results ends index op)) (placeholders : Bool)
    (initial : ∀ w, wgStoreView w.wg = wgStoreView (initialWG trace.net trace.bare) → I [] w) :
    S (runPrefixOuter (RxHistory.executeTraceWith call trace placeholders) []).2 := by
  have checked := (prefixOuter_wp_iff _ _ _ _).mp
    (executeTraceWith_wp I S safe store accept call calls trace traceCalls placeholders initial) [] rfl
  cases hr : runPrefixOuter (RxHistory.executeTraceWith call trace placeholders) [] with
  | mk result hist => cases result <;> simpa only [hr] using checked

end Leanux.Proofs.WG.RunnerInvariant.Shaped
