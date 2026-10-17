import Leanux.Proofs.WG.Queues.RxLinkEnvironment
import Leanux.Proofs.WG.Queues.RxCompletionRunner

/-! Initialized source/history linkage and independently checked receipt truth
on the existing Runner. Operational definitions, original erasure, full audit
projection and completion pairing are reused unchanged. Global committed order
does not label individual poll boundaries or assert admission conservation. -/
namespace Leanux.Proofs.WG.Queues.RxLink
open Lean Leanux Leanux.Env Leanux.Runner Leanux.Proofs.Logged Lifetimes Std.Do

variable {P : List RxHistory.Event → Prop} [Protocol P]

omit [Protocol P] in
theorem runAtHistory_wp {g : RxHistory.Obs α} (hg : Preserves P g)
    (index : Nat) (w : World) :
    ⦃fun h => ⌜P h⌝⦄ runAtPrefix index w g
    ⦃post⟨fun _ h => ⌜P h⌝,
      fun _ h => ⌜P h⌝⟩⦄ :=
  runAtPrefix_wp (show PrefixEnsures (fun h _ => P h)
    P g (fun _ h _ => P h) from hg) index w

/-- The actual Runner loops retain the history predicate at every returned
accumulator. Initialization and failed prefill emit no committed poll metadata. -/
theorem executeTraceHistory_protocol_wp (trace : Trace) (placeholders : Bool) :
    ⦃fun h => ⌜P h⌝⦄ RxHistory.executeTraceHistory trace placeholders
    ⦃post⟨fun _ h => ⌜P h⌝,
      fun _ h => ⌜P h⌝⟩⦄ :=
  RxCompletion.executeTraceWith_history_wp RxHistory.syscall trace placeholders
    (fun _ hi => hi)
    (fun index state call => runAtHistory_wp (syscall_preserves call) index state)
    (fun index state => runAtHistory_wp (lift_quiet skipAmbient) index state)

/-- Both successful and failed initialized executions retain the supplied
history-only protocol. No World premise or success assumption is introduced. -/
theorem executeTraceHistory_protocol (trace : Trace) (placeholders : Bool) (hi : P []) :
    P (runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []).2 := by
  have hs := (prefixOuter_wp_iff _ _ _ _).mp
    (executeTraceHistory_protocol_wp (P := P) trace placeholders) [] hi
  cases hr : runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) [] with
  | mk result hist => cases result <;> simpa only [hr] using hs

/-- Linkage and receipt truth are separate instances of the same concrete
caller proof. Empty initialization discharges both with no extra trace premise. -/
theorem executeTraceHistory_linkage (trace : Trace) (placeholders : Bool) :
    let h := (runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []).2
    HistoryLinked h ∧ HistoryReceiptsValid h :=
  ⟨executeTraceHistory_protocol (P := HistoryLinked) trace placeholders Linked.start,
    executeTraceHistory_protocol (P := HistoryReceiptsValid) trace placeholders (by simp [HistoryReceiptsValid,RxDisposition.Valid])⟩

/-- Every linked event has its own strict earlier prefix in the committed
history. The full receipt and Entry are retained, even if a later call Stops;
this global order alone does not identify an event's poll-local segment. -/
theorem executeTraceHistory_ordered (trace : Trace) (placeholders : Bool) :
    let h := (runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []).2.filterMap historyEvent
    ∀ event ∈ h, ∃ before after, h = before ++ [event] ++ after ∧ EventLink [] before event := by
  have hi := (executeTraceHistory_linkage trace placeholders).1
  obtain ⟨s,hs,he⟩ := hi.events
  simpa only [List.nil_append] using hs ▸ he

end Leanux.Proofs.WG.Queues.RxLink
