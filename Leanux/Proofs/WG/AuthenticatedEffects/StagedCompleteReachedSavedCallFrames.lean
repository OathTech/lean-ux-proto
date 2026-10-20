import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSavedCallSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedReadAccessFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSavedPeerAllocationFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProduct

namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SavedCall
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem Point.frame (point : Point pid next source w a v b) : StagedEntry.view v=StagedEntry.view w := by
  cases point with
  | reading point => rw [point.world]
  | body read point =>
      have prior := (hoare_iff_run_ambient _ _ _).mp
        (SavedFrames.read _ (·=StagedEntry.view _)) _ _ _ _ _ rfl read
      exact (point.frame prior.2).1.trans prior.1

theorem Point.allocation (point : Point pid next source w a v b)
    (before : AllocationInv history w) : AllocationInv history v := by
  cases point with
  | reading point => rw [point.world];exact before
  | body read point =>
      obtain ⟨rfl,_,d,device,resident⟩ := getPeer_normal _ _ _ _ _ _ read
      exact (point.allocation ⟨before,by simp [Peers.snapshot,device,resident]⟩).1

theorem Point.allocated (point : Point pid next source w a v b)
    (before : RetirementSecurity.StackOwnership.Allocated w) :
    RetirementSecurity.StackOwnership.Allocated v :=
  ⟨before.choose,point.allocation before.choose_spec⟩

theorem Point.carrier {w : World} (point : Point pid next source w.wg w.ambient v b)
    (before : CompleteProduct.Carrier h w) :
    CompleteProduct.Carrier h {w with wg:=v,ambient:=b} := by
  obtain ⟨ledger,account⟩:=before.1
  exact ⟨⟨ledger,account.same_view point.frame⟩,point.allocated before.2⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SavedCall
