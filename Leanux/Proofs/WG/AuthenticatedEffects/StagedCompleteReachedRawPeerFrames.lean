import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRawPeerSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingQueueRepaymentFrames

/-! A source-funded raw repayment cannot enter peer erasure or final finish.
Every fixed pre-erasure cut and normal return therefore retains the same
packet ledger and history, including the reference decrement itself. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RawPeer
open Leanux Leanux.WG Leanux.Proofs.Logged CompleteCarrier
open HandshakeSecurity.StagedDisposal PeerRetirement

theorem normal_accounted (before : Accounted h ledger debts locals w)
    (funded : Queued.Funded pid w)
    (performed : ((peerPut (some pid)).run w).run a=.ok (((),v),b)) :
    Accounted h ledger debts locals v := by
  obtain ⟨u,c,cut⟩:=AllocatedObligation.Publication.release_cut_nonfinal pid funded a
  rw [source,StateT.run_bind,StateT.run_bind,cut] at performed
  cases performed
  exact before.same_view (StagingPrimitive.release_none_view cut)

/-- An actually funded raw repayment keeps every packet in the same ledger
at each declared native cut; no final-release disposal is possible. -/
theorem Point.accounted (point : Point (some pid) w a v b)
    (before : Accounted h ledger debts locals w) (funded : Queued.Funded pid w) :
    Accounted h ledger debts locals v := by
  cases point with
  | entry=>exact before
  | native _ _ performed=>exact Points.Stage.accounted before performed
  | cut value performed=>
    have nonfinal:=StagingPrimitive.funded_release_none funded performed
    subst value
    exact before.same_view (StagingPrimitive.release_none_view performed)
  | finish _ _ _ cut _=>cases StagingPrimitive.funded_release_none funded cut
  | returned performed=>exact normal_accounted before funded performed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RawPeer
