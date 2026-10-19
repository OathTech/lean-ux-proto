import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteConsequencesSelectedAnchor

/-! Appending receipts retains the exact earlier take and its native census. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteSelected
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open HandshakeSecurity.StagedConservation

theorem NativeAnchor.append (before : NativeAnchor position history) (suffix : List Event) :
    NativeAnchor position (history ++ suffix) := by
  obtain ⟨r,locals,atCut,native⟩ := before
  have bound := (List.getElem?_eq_some_iff.mp atCut).1
  exact ⟨r,locals,by simpa [List.getElem?_append_left bound] using atCut,native⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteSelected
