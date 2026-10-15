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

theorem toSyscall_shape (results : Array Int) (ends : Array (Option (Nat × Nat)))
    (index : Nat) (op : Operation) (shape : OperationAddressShape op) :
    SyscallAddressShape (toSyscall results ends index op) := by
  cases op <;> simpa only [toSyscall, SyscallAddressShape, OperationAddressShape] using shape

private theorem global_kernel {h : List RoutingCompletion} {w v : World}
    (hi : GlobalCompletionState initial h w) (hk : v.k = w.k) :
    GlobalCompletionState initial h v := by
  simpa only [GlobalCompletionState, routingView, hk] using hi

theorem runAtCompletion_wp {g : PrefixM RoutingCompletion α}
    (hg : PrefixPreserves (GlobalCompletionState initial) (CompletionSafe initial) g)
    (index : Nat) (w : World) :
    ⦃fun h => ⌜GlobalCompletionState initial h w⌝⦄ runAtPrefix index w g
    ⦃post⟨fun out h => ⌜GlobalCompletionState initial h out.2⌝,
      fun _ h => ⌜CompletionSafe initial h⌝⟩⦄ :=
  runAtPrefix_wp (show PrefixEnsures (GlobalCompletionState initial)
    (CompletionSafe initial) g (fun _ => GlobalCompletionState initial) from hg) index w

private theorem shape_cursor (trace : Trace) (shape : TraceAddressShape trace)
    (pref : List Operation) (cur : Operation) (suff : List Operation)
    (h : trace.ops.toList = pref ++ cur :: suff) : OperationAddressShape cur :=
  shape cur (by rw [← Array.mem_toList_iff, h]; simp)

/-- The source-shaped post-initialization body preserves the actual accumulator
World. Array cursor membership supplies the shape of each executed operation. -/
theorem runnerTailObserved_wp (trace : Trace) (shape : TraceAddressShape trace) (w : World) :
    ⦃fun h => ⌜GlobalCompletionState ([], []) h w⌝⦄ runnerTailObserved trace w
    ⦃post⟨fun out h => ⌜GlobalCompletionState ([], []) h out.2⌝,
      fun _ h => ⌜CompletionSafe ([], []) h⌝⟩⦄ := by
  have syscall_spec (index : Nat) (w : World) (results : Array Int)
      (ends : Array (Option (Nat × Nat))) (op : Operation) (hs : OperationAddressShape op) :=
    runAtCompletion_wp (syscallObserved_global ([], []) _ (toSyscall_shape results ends index op hs)) index w
  have ambient_spec (index : Nat) (w : World) :=
    runAtCompletion_wp (global_completion_same ([], []) skipAmbient
      (routing_kernel _ skipAmbient_sameKernel)) index w
  unfold runnerTailObserved
  mvcgen [syscall_spec, ambient_spec]
  all_goals try exact
    ((post⟨fun out h => ⌜GlobalCompletionState ([], []) h out.2.1⌝,
      fun _ h => ⌜CompletionSafe ([], []) h⌝⟩) :
      Invariant trace.ops.toList
        (World × Array Int × Array (Option (Nat × Nat)) × Array Json × Array Json × Array Json)
        (.except (Nat × Stop) (.arg (List RoutingCompletion) .pure)))
  all_goals try
    let r : Unit × World := by assumption
    exact ((post⟨fun _ h => ⌜GlobalCompletionState ([], []) h r.2⌝,
      fun _ h => ⌜CompletionSafe ([], []) h⌝⟩) :
      Invariant r.2.steps.toList (Array Json)
        (.except (Nat × Stop) (.arg (List RoutingCompletion) .pure)))
  all_goals try
    let r : Unit × World := by assumption
    exact ((post⟨fun _ h => ⌜GlobalCompletionState ([], []) h r.2⌝,
      fun _ h => ⌜CompletionSafe ([], []) h⌝⟩) :
      Invariant r.2.fired.toList (Array Json)
        (.except (Nat × Stop) (.arg (List RoutingCompletion) .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try trivial
  all_goals try (solve | rename_i history hi; exact global_kernel hi rfl)
  all_goals try exact (show GlobalCompletionState ([], []) _ _ from by assumption).1
  all_goals try (solve | intros; assumption)
  all_goals try (solve | intros; exact (show GlobalCompletionState ([], []) _ _ from by assumption).1)
  all_goals exact shape_cursor trace shape _ _ _ (by assumption)

/-- Successful prefill supplies the actual initialized routing state; prefill
failure retains the empty safe journal and has no returned World. -/
theorem executeTraceObserved_wp (trace : Trace) (shape : TraceAddressShape trace)
    (placeholders : Bool) :
    ⦃fun h => ⌜h = []⌝⦄ executeTraceObserved trace placeholders
    ⦃post⟨fun out h => ⌜GlobalCompletionState ([], []) h out.2⌝,
      fun _ h => ⌜CompletionSafe ([], []) h⌝⟩⦄ := by
  have tail_spec (w : World) := runnerTailObserved_wp trace shape w
  unfold executeTraceObserved
  mvcgen [tail_spec]
  all_goals try dsimp +zetaDelta only at *
  all_goals try trivial
  all_goals
    rename_i history hh
    subst history
    first
    | exact global_initial trace _ rfl
    | exact global_initial_prefill trace _ (by assumption)
    | exact CompletionSafe.nil

/-- The actual initialized result retains valid completions on every outcome;
only a normal result supplies the final accumulator World. -/
theorem executeTraceObserved_routing (trace : Trace) (shape : TraceAddressShape trace)
    (placeholders : Bool) :
    CompletionSafe ([], []) (runPrefixOuter (executeTraceObserved trace placeholders) []).2 ∧
    ∀ out, (runPrefixOuter (executeTraceObserved trace placeholders) []).1 = .ok out →
      GlobalCompletionState ([], []) (runPrefixOuter (executeTraceObserved trace placeholders) []).2 out.2 := by
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
      GlobalCompletionState ([], []) (runPrefixOuter (executeTraceObserved trace placeholders) []).2 out.2 :=
  executeTraceObserved_routing trace (parseTrace_shape json trace parsed) placeholders

end Leanux.Proofs.WG.Configuration
