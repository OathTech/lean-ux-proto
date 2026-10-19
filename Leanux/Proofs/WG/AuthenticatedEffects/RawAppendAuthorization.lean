import Leanux.Proofs.WG.AuthenticatedEffects.RawAppendFinalOccurrences
import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionAuthorization

/-! Authorization for the independent original-append observer. The exact
whole-driver projection transfers each raw append's position, not merely its
datagram value, into the final causal journal. Its own earlier causal prefix
therefore supplies the authentication/fixture root or qualified cookie case,
including append occurrences before delivery clears or later Stops. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.RawAppend.Final
open Leanux Leanux.Proofs.Logged

theorem selected_added (event : CausalJournal.Event) (append : RawAppend.Event)
    (selected : raw? event = some append) : CausalJournal.Emissions.added event = [append.datagram] := by
  cases event <;> try (simp only [raw?] at selected; contradiction)
  case old event =>
    cases event <;> try (simp only [raw?,journal?] at selected; contradiction)
    case socket receipt => exact (selected_delta _ _ append selected).2
  case protocolSocket receipt => exact (selected_delta _ _ append selected).2
  case cookieSocket receipt =>
    simp only [raw?] at selected
    cases selected
    rfl

/-- Every original socket append has its own authenticated or fixture-rooted
cause, with only the qualified native cookie exception. The initialized
same-driver claim retains the exact raw ordinal and survives later Stop. -/
theorem initialized_authorized (trace : Runner.Trace) (placeholders : Bool)
    (before after : List RawAppend.Event) (append : RawAppend.Event)
    (position : (runPrefixOuter (RawAppend.execute trace placeholders) []).2 = before ++ append :: after) :
    ∃ pre event post,
      (runPrefixOuter (CausalJournal.execute trace placeholders) []).2 = pre ++ event :: post ∧
      pre.filterMap raw? = before ∧ raw? event = some append ∧ post.filterMap raw? = after ∧
      CausalJournal.Emissions.added event = [append.datagram] ∧
      CausalJournal.Emissions.AuthorizedAppend pre event := by
  obtain ⟨pre,event,post,atReceipt,prior,selected,later⟩ :=
    initialized_occurrence trace placeholders before after append position
  have singleton := selected_added event append selected
  exact ⟨pre,event,post,atReceipt,prior,selected,later,singleton,
    CausalJournal.Emissions.initialized_append trace placeholders pre post event atReceipt 0 append.datagram
      (by rw [singleton]; rfl)⟩

end Leanux.Proofs.WG.AuthenticatedEffects.RawAppend.Final
