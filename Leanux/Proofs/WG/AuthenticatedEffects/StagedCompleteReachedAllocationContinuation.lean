import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedAllocationReceipt
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPointResidual

/-! The native allocator's original take/drop cursor retains the captured
entry for the one batch receipt. Native prefix cells remain aliases until
that receipt, including the cut after the final native allocation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Allocation
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Staged.Obligations CompleteCarrier

def remainder (packets : List DataPacket) (count : Nat) (items : List SkbId)
    (origin : WGWorld) (clock : Ambient) : WGPrefix Event (List SkbId) :=
  Staging.Points.savedReceipt (fun run=>.old (.allocated packets run)) origin clock
    (liftWGPrefix (do
      let rest←(packets.drop count).mapM newTxSkb
      pure (items++rest)))

/-- Every literal allocator cursor resumes the original receipt, preserving
the invocation's before-world and ordered complete item list. Totality is
derived from the selected entry, not assumed from a completed caller. -/
theorem Interval.residual
    (cut : Interval history ledger debts locals generation pid peer position kid packets w a n items v) :
    runWGPrefix (state (Journal.allocate packets)) w a history=
      runWGPrefix (remainder packets n items w a) v a history := by
  obtain ⟨allItems,target,performed,native,_,_,_,_⟩:=allocate_intervals cut.entry cut.shape
  obtain ⟨rest,remaining,ordered⟩:=cut.path.remaining native
  dsimp only at remaining ordered
  rw [performed]
  simp [remainder,Staging.Points.savedReceipt,runWGPrefix_receiptWGObserved,
    runWGPrefix_lift,remaining,ordered]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Allocation
