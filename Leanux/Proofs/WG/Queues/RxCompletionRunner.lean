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


private theorem historyOuter_pure {E α : Type} {P S : List E → Prop} (x : α) :
    ⦃fun h => ⌜P h⌝⦄ (pure x : PrefixOuter E α)
    ⦃post⟨fun _ h => ⌜P h⌝, fun _ h => ⌜S h⌝⟩⦄ := by
  apply (prefixOuter_wp_iff _ _ _ _).mpr
  exact fun _ hi => hi

private theorem historyOuter_throw {E α : Type} {P S : List E → Prop}
    (hs : ∀ h, P h → S h) (e : Nat × Stop) :
    ⦃fun h => ⌜P h⌝⦄ (throw e : PrefixOuter E α)
    ⦃post⟨fun _ h => ⌜P h⌝, fun _ h => ⌜S h⌝⟩⦄ := by
  apply (prefixOuter_wp_iff _ _ _ _).mpr
  exact hs

private theorem historyOuter_bind {E α β : Type} {P S : List E → Prop}
    {g : PrefixOuter E α} {f : α → PrefixOuter E β}
    (hg : ⦃fun h => ⌜P h⌝⦄ g
      ⦃post⟨fun _ h => ⌜P h⌝, fun _ h => ⌜S h⌝⟩⦄)
    (hf : ∀ x, ⦃fun h => ⌜P h⌝⦄ f x
      ⦃post⟨fun _ h => ⌜P h⌝, fun _ h => ⌜S h⌝⟩⦄) :
    ⦃fun h => ⌜P h⌝⦄ (g >>= f)
    ⦃post⟨fun _ h => ⌜P h⌝, fun _ h => ⌜S h⌝⟩⦄ :=
  Triple.bind g f hg hf

private theorem historyOuter_array {E α β : Type} {P S : List E → Prop}
    (xs : Array α) (init : β) (body : α → β → PrefixOuter E (ForInStep β))
    (hb : ∀ x acc, ⦃fun h => ⌜P h⌝⦄ body x acc
      ⦃post⟨fun _ h => ⌜P h⌝, fun _ h => ⌜S h⌝⟩⦄) :
    ⦃fun h => ⌜P h⌝⦄ forIn xs init body
    ⦃post⟨fun _ h => ⌜P h⌝, fun _ h => ⌜S h⌝⟩⦄ := by
  rw [← Array.forIn_toList]
  generalize xs.toList = ys
  induction ys generalizing init with
  | nil => simpa only [List.forIn_nil] using historyOuter_pure init
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply historyOuter_bind (hb x init)
    intro step
    cases step with
    | done acc => exact historyOuter_pure acc
    | yield acc => exact ih acc

/- The target action is inspected before every composition rule. Pure JSON
values are never traversed to select a history invariant. -/
macro "history_outer_steps" hs:term : tactic => `(tactic| first
  | (runner_wp_head Pure.pure; exact historyOuter_pure _)
  | (runner_wp_head throw; exact historyOuter_throw $hs _)
  | runner_wp_throw_bind
  | (runner_wp_head Bind.bind; apply historyOuter_bind)
  | (runner_wp_head ForIn.forIn; apply historyOuter_array)
  | runner_wp_reduce
  | ((first | runner_wp_head ite | runner_wp_head dite); split)
  | maintenance_intro
  | runner_wp_match)

/-- The literal runner tail preserves a history predicate on success and its
stated failed-history consequence at every indexed Stop. The syscall observer
and both history predicates are arbitrary. -/
theorem runnerTail_history_wp {E : Type} {P S : List E → Prop}
    (call : Syscall → PrefixM E Int) (trace : Trace) (w : World)
    (hs : ∀ h, P h → S h)
    (hc : ∀ index state op,
      ⦃fun h => ⌜P h⌝⦄ runAtPrefix index state (call op)
      ⦃post⟨fun _ h => ⌜P h⌝, fun _ h => ⌜S h⌝⟩⦄)
    (ha : ∀ index state,
      ⦃fun h => ⌜P h⌝⦄ runAtPrefix index state (liftPrefix (skipAmbient : Leanux.M Unit))
      ⦃post⟨fun _ h => ⌜P h⌝, fun _ h => ⌜S h⌝⟩⦄) :
    ⦃fun h => ⌜P h⌝⦄ RxHistory.runnerTail call trace w
    ⦃post⟨fun _ h => ⌜P h⌝, fun _ h => ⌜S h⌝⟩⦄ := by
  unfold RxHistory.runnerTail
  repeat' first
    | (runner_wp_head runAtPrefix; first | exact hc _ _ _ | exact ha _ _)
    | history_outer_steps hs

/-- Initial prefill and routing trials commit no history. The actual runner
then executes its literal tail with the supplied product syscall observer. -/
theorem executeTraceWith_history_wp {E : Type} {P S : List E → Prop}
    (call : Syscall → PrefixM E Int) (trace : Trace) (placeholders : Bool)
    (hs : ∀ h, P h → S h)
    (hc : ∀ index state op,
      ⦃fun h => ⌜P h⌝⦄ runAtPrefix index state (call op)
      ⦃post⟨fun _ h => ⌜P h⌝, fun _ h => ⌜S h⌝⟩⦄)
    (ha : ∀ index state,
      ⦃fun h => ⌜P h⌝⦄ runAtPrefix index state (liftPrefix (skipAmbient : Leanux.M Unit))
      ⦃post⟨fun _ h => ⌜P h⌝, fun _ h => ⌜S h⌝⟩⦄) :
    ⦃fun h => ⌜P h⌝⦄ RxHistory.executeTraceWith call trace placeholders
    ⦃post⟨fun _ h => ⌜P h⌝, fun _ h => ⌜S h⌝⟩⦄ := by
  unfold RxHistory.executeTraceWith
  repeat' first
    | (runner_wp_head RxHistory.runnerTail; exact runnerTail_history_wp _ _ _ hs hc ha)
    | history_outer_steps hs

/-- The actual Runner's loops retain the protocol at every returned accumulator;
initialization and failed prefill leave the empty callback history untouched. -/
theorem executeTraceHistory_completion_wp (trace : Trace) (placeholders : Bool) :
    ⦃fun h => ⌜Closed historyEvent h⌝⦄ RxHistory.executeTraceHistory trace placeholders
    ⦃post⟨fun _ h => ⌜Closed historyEvent h⌝,
      fun _ h => ⌜CompletionPrefix historyEvent h⌝⟩⦄ :=
  executeTraceWith_history_wp RxHistory.syscall trace placeholders
    (fun _ hi => hi.prefix)
    (fun index state call => runAtCompletion_wp (syscall_preserves call) index state)
    (fun index state =>
      runAtCompletion_wp (lift_quiet (ρ := historyEvent) skipAmbient) index state)

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
