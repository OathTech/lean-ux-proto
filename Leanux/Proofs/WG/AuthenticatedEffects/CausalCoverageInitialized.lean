import Leanux.Proofs.WG.AuthenticatedEffects.CausalCoverageOuter
import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptInitialized

/-! No actual initialized delayed effect or TX allocation is left without a
lexical context. These positions belong to the final journal, not an erased
history or an arbitrary native invocation. Authorization remains separate. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
open Leanux Leanux.WG Leanux.Proofs.Logged

theorem initialized_present (trace : Runner.Trace) (placeholders : Bool)
    (before after : List Event) (event : Event)
    (position : (runPrefixOuter (execute trace placeholders) []).2 = before ++ event :: after)
    (relevant : Protected event) : Present before :=
  initialized trace placeholders before event after position relevant

theorem arm_context (trace : Runner.Trace) (placeholders : Bool)
    (before after : List Event) (receipt : TimerEffects.Arm Context)
    (position : (runPrefixOuter (execute trace placeholders) []).2 = before ++ .armed receipt :: after) :
    ∃ token, receipt.cause = .ok (some token) ∧ CausalScope.current scope? before = .ok (some token) := by
  obtain ⟨token,current⟩ := initialized_present trace placeholders before after (.armed receipt) position True.intro
  exact ⟨token,(Receipts.initialized_arm trace placeholders before after receipt position).2.trans current,current⟩

theorem queue_context (trace : Runner.Trace) (placeholders : Bool)
    (before after : List Event) (receipt : TimerEffects.Queued Context)
    (position : (runPrefixOuter (execute trace placeholders) []).2 = before ++ .queued receipt :: after) :
    ∃ token, receipt.cause = .ok (some token) ∧ CausalScope.current scope? before = .ok (some token) := by
  obtain ⟨token,current⟩ := initialized_present trace placeholders before after (.queued receipt) position True.intro
  exact ⟨token,(Receipts.initialized_queue trace placeholders before after receipt position).2.trans current,current⟩

theorem allocation_context (trace : Runner.Trace) (placeholders : Bool)
    (before after : List Event) (packets : List DataPacket) (run : WGRunWitness (List SkbId))
    (position : (runPrefixOuter (execute trace placeholders) []).2 = before ++ .old (.allocated packets run) :: after) :
    Present before :=
  initialized_present trace placeholders before after (.old (.allocated packets run)) position True.intro

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
