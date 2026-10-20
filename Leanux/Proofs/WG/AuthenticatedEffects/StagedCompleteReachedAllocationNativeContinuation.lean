import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedAllocationNativeFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedAllocationContinuation

/-! Adapter interiors resume the exact saved allocation capture. Their
native suffix comes from the source point, rather than replaying an earlier
iteration merely because it has the same WG projection. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Allocation
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity CausalJournal

noncomputable def nativeRemainder (point : Point packets w a v b) : WGPrefix Event (List SkbId) :=
  Staging.Points.savedReceipt (fun run=>.old (.allocated packets run)) w a
    (liftWGPrefix (Classical.choose point.remaining))

theorem nativeRemainder_run (device : w.dev=some d) (point : Point packets w a v b) :
    runWGPrefix (state (Journal.allocate packets)) w a h=
      runWGPrefix (nativeRemainder point) v b h := by
  obtain ⟨items,target,_,_,performed⟩ := Staged.Obligations.HeldFrontier.allocate_total packets w a device
  have remaining := (Classical.choose_spec point.remaining).symm.trans performed
  rw [Staged.Obligations.HeldFrontier.allocation_observed packets w target a a items performed h]
  simp [nativeRemainder,Staging.Points.savedReceipt,runWGPrefix_receiptWGObserved,
    runWGPrefix_lift,remaining]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Allocation
