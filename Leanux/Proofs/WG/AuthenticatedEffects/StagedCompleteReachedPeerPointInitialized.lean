import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerPointComposition
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerFinishInitialized

/-! Fixed release points inside actual initialized encryption publication.
The enclosing receipt retains its original invocation world, and every native
point keeps the same ledger or its exact pending-release successor. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues TransmitSecurity CausalJournal RunnerSource AllocatedObligation
open EncryptionPacket EncryptionInterior PeerRetirement
variable {state : PacketState}

theorem EncryptionRun.Entry.publication_release_point
    (entry : EncryptionRun.Entry trace placeholders operationIndex (some items) world history)
    (path : PublicationPath items world history ledger [] [] headId head state v after)
    (published : PublicationPoint .scheduled items state ledger [] [] v after first pid next last)
    (point : Points.LiftedPoint (some pid) next last cut middle) :
    Points.Evidence ledger [] [] middle cut.wg ∧
    runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
      (fun result w=>(result,w)) trace placeholders) [] =
      runPrefixOuter (entry.resume cut
        (EncryptionRun.returned world items (do point.remainder; pure true))) middle := by
  refine ⟨point.evidence published.accounted,?_⟩
  rw [entry.publication_interior_continuation path published]
  apply entry.resume_run_eq
  apply EncryptionRun.returned_congr
  exact Scheduler.bind_run_equal (fun _=>pure true) point.continuation

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
