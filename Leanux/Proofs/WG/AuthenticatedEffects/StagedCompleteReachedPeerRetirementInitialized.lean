import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerRetirementContinuation
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedEncryptPublicationInteriors
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTransmitResidualInitialized

/-! Release's actual native cuts occur in the initialized publication and
routed-front callers. The original ticket cohort survives silently until
its own counted receipt, with releaseFinish still the remaining native child. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CausalJournal RunnerSource
open EncryptionPacket EncryptionInterior PeerRetirement
variable {state : PacketState}

theorem EncryptionRun.Entry.publication_release_continuation
    (entry : EncryptionRun.Entry trace placeholders operationIndex (some items) world history)
    (path : PublicationPath items world history ledger [] [] headId head state v after)
    (point : PublicationPoint .scheduled items state ledger [] [] v after first pid next last)
    (performed : ((prefixAt site (some pid)).run next.wg).run next.ambient=.ok ((value,g),clock)) :
    runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
      (fun result w=>(result,w)) trace placeholders) [] =
      runPrefixOuter (entry.resume {next with wg:=g,ambient:=clock}
        (EncryptionRun.returned world items (do
          liftWGObserver (remaining (some pid) next.wg next.ambient (tailAt site value))
          pure true))) last := by
  rw [entry.publication_interior_continuation path point]
  apply entry.resume_run_eq
  apply EncryptionRun.returned_congr
  exact Scheduler.bind_run_equal (fun _=>pure true) (point_lifted performed)

theorem RoutedTransmit.Caller.release_settlement
    (caller : RoutedTransmit.Caller trace placeholders operationIndex world history)
    (selected : Transmit.Front.Selected caller.input (Transmit.inputHistory caller.input caller.events)
      caller.entered.wg caller.entered.ambient (.release (some pid) code) u c)
    (device : u.dev=some d) (resident : d.peers[pid]?=some p)
    (tested : (testAmbient p.refcount).run (entryClock c)=.ok (true,b))
    (quiet : queued p=false) :
    ∃ ledger,
      let original := Transmit.inputHistory caller.input caller.events
      let tickets := cohort ledger pid p d
      let final := finalWorld pid p d u
      let clock := indexClock pid d b
      ((HandshakeSecurity.StagedDisposal.releaseCut (some pid)).run u).run c=
        .ok ((some (pid,p),final),clock) ∧
      Staged.Origins.Aligned
        (Staged.Origins.Born original d.ifindex pid p.internalId) tickets p.staged ∧
      Staged.stagedAt final pid=none ∧
      Staged.dropped final=some (d.txDropped+tickets.length) ∧
      CompleteCarrier.Accounted (original++[releaseEvent (some pid) (some (pid,p)) u final c clock])
        (Staged.Obligations.settle tickets (.counted original.length .finalRelease) ledger) [] [] final := by
  obtain ⟨ledger,before⟩ := caller.selected_account selected
  obtain ⟨native,aligned,erased,charged⟩ := release_pending before device resident tested quiet
  exact ⟨ledger,native,aligned,erased,charged,(release_accounted before device resident tested quiet).1⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
