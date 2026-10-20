import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerCreationFrames

/-! Fixed creation source points preserve the identical ticket ledger.
Freshness is derived at the original front, not supplied at each cut. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerCreation
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal Queues.RxCredits

theorem Point.accounted (before : CompleteCarrier.Accounted h ledger [] [] w)
    (bounded : PeerSlotsBounded w) (point : Point key psk w a v b) : CompleteCarrier.Accounted h ledger [] [] v := by
  cases point with
  | front point=>exact before.same_view point.frame
  | core prepared point=>
      obtain ⟨rfl,vacant⟩:=front_admitted bounded prepared
      exact point.accounted before vacant
  | tail prepared created point=>
      obtain ⟨rfl,vacant⟩:=front_admitted bounded prepared
      exact (core_account before vacant created).same_view point.frame
  | returned performed=>
      exact ⟨((hoare_iff_run_ambient _ _ _).mp (PeerCreationFrames.create key psk) _ _ _ _ _ ⟨before.entry,bounded⟩ performed).1,before.complete⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerCreation
