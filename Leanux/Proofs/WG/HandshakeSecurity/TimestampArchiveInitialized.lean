import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveDispatch
import Leanux.Proofs.WG.HandshakeSecurity.TimestampDriverProjection
import Leanux.Proofs.WG.Origins.RunnerInvariant

/-! Allocation-indexed timestamp freshness on the initialized native runner.
The archive includes committed writes preceding an indexed Stop. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity

theorem initialized (trace : Runner.Trace) (placeholders : Bool) :
    History (runPrefixOuter (TimestampDriver.execute trace placeholders) []).2 := by
  apply RunnerInvariant.executeTraceWith ProductInv History
    (fun _ _ hi => hi.1) product_wg_stable (Driver.syscallObserved TimestampDriver.hooks)
    syscall trace placeholders
  intro w same
  apply product_wg_stable [] {w with wg := Runner.initialWG trace.net trace.bare} w same
  exact state_initial trace.net trace.bare

theorem History.checked {history : List TimestampReceipt} (safe : History history)
    (pre post : List TimestampReceipt) (r : TimestampReceipt)
    (position : history = pre ++ r :: post) : r.Valid ∧ Linked (replay pre) r := by
  induction safe generalizing pre post r with
  | empty => cases pre <;> cases position
  | @next history receipt prior valid linked ih =>
    apply (pinned_const _private.Leanux.Proofs.WG.Origins.HistorySupport.«0».Leanux.Proofs.WG.Origins.HistorySupport.positions_append)
      (fun pre r => r.Valid ∧ Linked (replay pre) r) history [receipt]
      (fun pre r post position => ih pre post r position) ?_ pre r post position
    intro before event after single
    cases before with
    | nil => cases single; simpa only [List.append_nil] using And.intro valid linked
    | cons x xs =>
      have lengths := congrArg List.length single
      simp only [List.length_append,List.length_cons,List.length_nil] at lengths
      omega

/-- Every actual committed timestamp compares against the archived timestamp
of its peer allocation, not an assumed adjacent call or a numeric peer slot.
There is no incoming archive or reachability premise. -/
theorem initialized_cut (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List TimestampReceipt) (r : TimestampReceipt)
    (position : (runPrefixOuter (TimestampDriver.execute trace placeholders) []).2 = pre ++ r :: post) :
    r.Valid ∧ Linked (replay pre) r :=
  (initialized trace placeholders).checked pre post r position

/-- Once this allocation has an archived timestamp, its next committed write
must strictly increase it. The previous value is read from this same actual
execution prefix; peer deletion and slot reuse cannot reset that archive. -/
theorem initialized_advances_archive (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List TimestampReceipt) (r : TimestampReceipt)
    (position : (runPrefixOuter (TimestampDriver.execute trace placeholders) []).2 = pre ++ r :: post)
    (identity : Nat) (old : List UInt8)
    (allocation : (freshnessAt r.execution.before r.peer).map Prod.fst = some identity)
    (archived : replay pre identity = some old) : memcmp r.received old = .gt := by
  obtain ⟨stamp,previous,resident,linked,increase⟩ := (initialized_cut trace placeholders pre post r position).2
  have equal : stamp = identity := by simpa only [resident,Option.map_some,Option.some.injEq] using allocation
  subst stamp
  rcases linked with absent | current
  · rw [archived] at absent; cases absent
  · have same : previous = old := Option.some.inj (current.symm.trans archived)
    simpa only [same] using increase

end Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
