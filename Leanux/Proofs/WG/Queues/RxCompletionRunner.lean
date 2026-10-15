import Leanux.Proofs.WG.Queues.RxCompletionEnvironment
import Leanux.Proofs.WG.Queues.RxRunnerHistory

/-! Initialized callback return pairing on the existing stamped Runner. This is
normal Stack return, not socket arrival or receive-pipeline conservation. Failed
prefixes retain valid receipts and at most one unfinished trailing entry. -/
namespace Leanux.Proofs.WG.Queues.RxCompletion
open Lean Leanux Leanux.Env Leanux.Runner Leanux.Proofs.Logged Lifetimes Std.Do

/-- Completed receipts remain valid even when the enclosing execution stops. -/
theorem PrefixTrace.receipts (ht : PrefixTrace t) :
    ∀ e r, Step.completed e r ∈ t → r.Valid (Stack.receive e.tag.bytes) := by
  rcases ht with hc | ⟨pre, last, hc, rfl⟩
  · exact hc.receipts
  · intro e r hm
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hm | bad
    · exact hc.receipts e r hm
    · cases bad

/-- Receipt stamps inherit distinctness from actual callback-entry stamps,
including a prefix ending inside its last callback. -/
theorem PrefixTrace.completed_nodup (ht : PrefixTrace t)
    (hn : ((t.filterMap entered).map RxJoint.Entry.stamp).Nodup) :
    ((t.filterMap completed).map RxJoint.Entry.stamp).Nodup := by
  rcases ht with hc | ⟨pre, last, hc, rfl⟩
  · rw [← hc.matches]
    exact hn
  · simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
      entered, completed, List.append_nil, List.map_append, List.map_cons, List.map_nil] at hn ⊢
    rw [← hc.matches]
    exact (List.nodup_append.mp hn).1

theorem runAtCompletion_wp {g : RxHistory.Obs α} (hg : Preserves historyEvent g)
    (index : Nat) (w : World) :
    ⦃fun h => ⌜Closed historyEvent h⌝⦄ runAtPrefix index w g
    ⦃post⟨fun _ h => ⌜Closed historyEvent h⌝,
      fun _ h => ⌜CompletionPrefix historyEvent h⌝⟩⦄ :=
  runAtPrefix_wp (show PrefixEnsures (fun h _ => Closed historyEvent h)
    (CompletionPrefix historyEvent) g (fun _ h _ => Closed historyEvent h) from hg) index w

/-- The actual Runner's loops retain the protocol at every returned accumulator;
initialization and failed prefill leave the empty callback history untouched. -/
theorem executeTraceHistory_completion_wp (trace : Trace) (placeholders : Bool) :
    ⦃fun h => ⌜Closed historyEvent h⌝⦄ RxHistory.executeTraceHistory trace placeholders
    ⦃post⟨fun _ h => ⌜Closed historyEvent h⌝,
      fun _ h => ⌜CompletionPrefix historyEvent h⌝⟩⦄ := by
  have syscall_spec (index : Nat) (w : World) (call : Syscall) :=
    runAtCompletion_wp (syscall_preserves call) index w
  have ambient_spec (index : Nat) (w : World) :=
    runAtCompletion_wp (lift_quiet (ρ := historyEvent) skipAmbient) index w
  unfold RxHistory.executeTraceHistory RxHistory.executeTraceWith RxHistory.runnerTail
  mvcgen [syscall_spec, ambient_spec]
  all_goals try exact
    ((post⟨fun _ h => ⌜Closed historyEvent h⌝,
      fun _ h => ⌜CompletionPrefix historyEvent h⌝⟩) :
      Invariant trace.ops.toList
        (World × Array Int × Array (Option (Nat × Nat)) × Array Json × Array Json × Array Json)
        (.except (Nat × Stop) (.arg (List RxHistory.Event) .pure)))
  all_goals try
    let r : Unit × World := by assumption
    exact ((post⟨fun _ h => ⌜Closed historyEvent h⌝,
      fun _ h => ⌜CompletionPrefix historyEvent h⌝⟩) :
      Invariant r.2.steps.toList (Array Json)
        (.except (Nat × Stop) (.arg (List RxHistory.Event) .pure)))
  all_goals try
    let r : Unit × World := by assumption
    exact ((post⟨fun _ h => ⌜Closed historyEvent h⌝,
      fun _ h => ⌜CompletionPrefix historyEvent h⌝⟩) :
      Invariant r.2.fired.toList (Array Json)
        (.except (Nat × Stop) (.arg (List RxHistory.Event) .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try trivial
  all_goals try exact Closed.prefix (by assumption)
  all_goals try (solve | intros; assumption)
  all_goals try (solve | intros; exact Closed.prefix (by assumption))

/-- All typed traces and both placeholder settings satisfy the protocol, on success or Stop.
No allocation, parser, credit, residency or progress premise is required. -/
theorem executeTraceHistory_completion (trace : Trace) (placeholders : Bool) :
    let out := runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []
    CompletionPrefix historyEvent out.2 ∧
      ∀ result, out.1 = .ok result → Closed historyEvent out.2 := by
  have hs := (prefixOuter_wp_iff _ _ _ _).mp
    (executeTraceHistory_completion_wp trace placeholders) [] ClosedTrace.nil
  cases hr : runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) [] with
  | mk result hist =>
    cases result with
    | error stop =>
      simp only [hr] at hs ⊢
      exact ⟨hs, by intros; contradiction⟩
    | ok result =>
      simp only [hr] at hs ⊢
      exact ⟨hs.prefix, fun _ _ => hs⟩

/-- Receipt validity and stamp uniqueness hold in every reached committed
history; normal return additionally matches the complete ordered entry list. -/
theorem executeTraceHistory_receipts (trace : Trace) (placeholders : Bool) :
    let out := runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []
    let t := out.2.filterMap historyEvent
    (∀ e r, Step.completed e r ∈ t → r.Valid (Stack.receive e.tag.bytes)) ∧
    ((t.filterMap completed).map RxJoint.Entry.stamp).Nodup ∧
    (∀ result, out.1 = .ok result → RxHistory.entries out.2 = t.filterMap completed) := by
  have hp := executeTraceHistory_completion trace placeholders
  have hn := (RxHistory.executeTraceHistory_safe trace placeholders).2
  refine ⟨PrefixTrace.receipts hp.1, PrefixTrace.completed_nodup hp.1 ?_, ?_⟩
  · simpa only [history_entries, RxHistory.stamps] using hn
  · intro result hr
    simpa only [history_entries] using (hp.2 result hr).matches

end Leanux.Proofs.WG.Queues.RxCompletion
