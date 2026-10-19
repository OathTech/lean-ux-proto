import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerFinishCoverage
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerRetirementInitialized

/-! The initialized publication's actual final release reaches its timer
guard and both identity writes after the same disposal receipt. The enclosing
encryption return keeps its original invocation world throughout. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues TransmitSecurity CausalJournal RunnerSource AllocatedObligation
open EncryptionPacket EncryptionInterior PeerRetirement
variable {state : PacketState}

theorem PeerRetirement.Finish.release_lifted
    (native : ((HandshakeSecurity.StagedDisposal.releaseCut peer).run w.wg).run w.ambient=
      .ok ((some (pid,p),v),b))
    (performed : ((Finish.prefixAt site pid p).run v).run b=.ok (((),g),c)) :
    runPrefix (liftWGObserver (CausalJournal.peerRelease peer)) w history=
      runPrefix (liftWGObserver (liftWGPrefix (Finish.tailAt site pid))) {w with wg:=g,ambient:=c}
        (history++[releaseEvent peer (some (pid,p)) w.wg v w.ambient b]) := by
  rw [liftWGObserver_run,liftWGObserver_run,Finish.release_continuation native performed]

theorem EncryptionRun.Entry.publication_finish_continuation
    (entry : EncryptionRun.Entry trace placeholders operationIndex (some items) world history)
    (path : PublicationPath items world history ledger [] [] headId head state v after)
    (point : PublicationPoint .scheduled items state ledger [] [] v after first pid next last)
    (native : ((HandshakeSecurity.StagedDisposal.releaseCut (some pid)).run next.wg).run next.ambient=
      .ok ((some (owner,p),g),clock))
    (performed : ((Finish.prefixAt site owner p).run g).run clock=.ok (((),cut),cutClock)) :
    runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
      (fun result w=>(result,w)) trace placeholders) [] =
      runPrefixOuter (entry.resume {next with wg:=cut,ambient:=cutClock}
        (EncryptionRun.returned world items (do
          liftWGObserver (liftWGPrefix (Finish.tailAt site owner))
          pure true)))
        (last++[releaseEvent (some pid) (some (owner,p)) next.wg g next.ambient clock]) := by
  rw [entry.publication_interior_continuation path point]
  apply entry.resume_run_eq
  apply EncryptionRun.returned_congr
  exact Scheduler.bind_run_equal (fun _=>pure true) (Finish.release_lifted native performed)

theorem EncryptionRun.Entry.publication_finish_interiors
    (entry : EncryptionRun.Entry trace placeholders operationIndex (some items) world history)
    (path : PublicationPath items world history ledger [] [] headId head state v after)
    (point : PublicationPoint .scheduled items state ledger [] [] v after first pid next last)
    (native : ((HandshakeSecurity.StagedDisposal.releaseCut (some pid)).run next.wg).run next.ambient=
      .ok ((some (owner,p),g),clock)) :
    ∃ settled,
      Staged.Obligations.Step ledger settled ∧ Staged.Obligations.AllocatedFrame ledger settled ∧
      let recorded := last++[releaseEvent (some pid) (some (owner,p)) next.wg g next.ambient clock]
      CompleteCarrier.Accounted recorded settled [] [] g ∧
      Finish.Cases owner p g clock (((HandshakeSecurity.StagedDisposal.releaseFinish owner p).run g).run clock) ∧
      (Finish.pending p=none → ∀ site : Finish.Site,
        CompleteConsequences.Cut recorded settled [] [] (Finish.atWorld site owner g) ∧
        runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
          (fun result w=>(result,w)) trace placeholders) [] =
          runPrefixOuter (entry.resume
            {next with wg:=Finish.atWorld site owner g,ambient:=Finish.atClock site owner clock}
            (EncryptionRun.returned world items (do
              liftWGObserver (liftWGPrefix (Finish.tailAt site owner))
              pure true))) recorded) := by
  obtain ⟨settled,step,frame,_,accounted,cases,points⟩ := Finish.after_release point.accounted native
  refine ⟨settled,step,frame,accounted,cases,?_⟩
  intro quiet site
  obtain ⟨performed,atCut,_⟩ := points quiet site
  exact ⟨CompleteConsequences.accounted atCut,entry.publication_finish_continuation path point native performed⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
