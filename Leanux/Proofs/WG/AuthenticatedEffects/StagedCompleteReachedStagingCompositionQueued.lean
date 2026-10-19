import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPrimitiveQueue

/-! The queued-initiation cuts are reached after the actual rejected
selection and ordered restore. The selected-to-staged transfer changes the
same ledger; no new cohort or idle account is supplied by a caller. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingComposition
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Staged.Obligations CompleteCarrier Staging Staging.Points StagingPhase StagingPrimitive
set_option maxHeartbeats 600000

theorem queued_from_restoration
    (before : Accounted h ledger debts locals w)
    (selected : runWGPrefix (CausalJournal.selection pid) w a h=(.ok ((some (peer,key),u),b),middle))
    (guarded : runWGPrefix (allocationPrefix pid peer key) u b middle=(.ok ((.rejected rejectedKey invalid,q),c),events))
    (prefixRun : runWGPrefix (RestoreEntry.prefixWith (m:=WGPrefix Event) liftWGPrefix peer.staged rejectedKey invalid)
      q c events=(.ok (((),t),e),prior))
    (restoreRun : runWGPrefix (CausalJournal.stagedRestore pid peer.staged) t e prior=(.ok (((),restored),clock),recorded))
    (point : QueuePoint pid restored clock recorded v d last rest) :
    ∃ after generation,
      Staged.Obligations.Step ledger (HeldFrontier.restoredLedger after generation pid peer h.length) ∧
      Accounted last (HeldFrontier.restoredLedger after generation pid peer h.length) debts locals v ∧
      runWGPrefix (Driver.stagingObserved hooks pid) w a h=runWGPrefix rest v d last := by
  obtain ⟨after,generation,path⟩:=callback_entry before selected guarded
  have steps : Staged.Obligations.Step ledger after := by
    obtain ⟨r,_,_,_,_,_,transferred,_⟩:=path.selected
    exact transferred.symm ▸ transferLocation_step _ _ _
  have ready:=(reject_prefix_covers peer.staged rejectedKey invalid path.ready).normal prefixRun
  have account:=Staging.normal (CompleteSelected.restore after debts locals generation pid peer h.length
    (fun _=>True) (fun _ _ _=>True.intro)) ready restoreRun
  refine ⟨after,generation,steps.trans (transferLocation_step _ _ _),point.accounted account,?_⟩
  have original := (callbackPoint selected guarded).residual
  change runWGPrefix (Driver.stagingObserved hooks pid) w a h=
    runWGPrefix (HeldSource.noKey pid peer rejectedKey invalid) q c events at original
  rw [rejection_factor,run_bind,prefixRun] at original
  dsimp only at original
  unfold rejectedTail at original
  rw [run_bind,restoreRun] at original
  exact original.trans point.residual

theorem keepalive_queued_from_restoration
    (before : Accounted h ledger debts locals w)
    (prepared : runWGPrefix (CausalJournal.keepalivePrepare pid) w a h=(.ok ((true,u),b),middle))
    (selected : runWGPrefix (CausalJournal.selection pid) u b middle=(.ok ((some (peer,key),q),c),events))
    (guarded : runWGPrefix (allocationPrefix pid peer key) q c events=(.ok ((.rejected rejectedKey invalid,t),e),prior))
    (prefixRun : runWGPrefix (RestoreEntry.prefixWith (m:=WGPrefix Event) liftWGPrefix peer.staged rejectedKey invalid)
      t e prior=(.ok (((),nativeWorld),nativeClock),nativeHistory))
    (restoreRun : runWGPrefix (CausalJournal.stagedRestore pid peer.staged) nativeWorld nativeClock nativeHistory=
      (.ok (((),restored),clock),recorded))
    (point : QueuePoint pid restored clock recorded v d last rest) :
    ∃ entered after generation,
      KeepaliveChange h ledger pid ⟨true,w,u,a,b⟩ entered ∧
      Staged.Obligations.Step entered (HeldFrontier.restoredLedger after generation pid peer middle.length) ∧
      Accounted last (HeldFrontier.restoredLedger after generation pid peer middle.length) debts locals v ∧
      runWGPrefix (Driver.keepaliveObserved hooks pid) w a h=runWGPrefix rest v d last := by
  obtain ⟨_,_,entered,account,change⟩:=keepalive_entry before prepared
  obtain ⟨after,generation,steps,atPoint,original⟩:=
    queued_from_restoration account selected guarded prefixRun restoreRun point
  exact ⟨entered,after,generation,change,steps,atPoint,(keepalivePoint prepared).residual.trans original⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingComposition
