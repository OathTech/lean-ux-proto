import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingCompositionCleanup
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreateCompositionRelease

/-! Actual TX staging reaches the nested access-bearing peer release on
its selected and allocated ticket lineage. Native erasure retains the two
original pending records and the literal remaining caller computation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingComposition
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Staged.Obligations CompleteCarrier Staging Staging.Points StagingPhase

theorem release_from_submission
    (before : Accounted h ledger debts locals w)
    (selected : runWGPrefix (CausalJournal.selection pid) w a h=(.ok ((some (peer,key),u),b),middle))
    (guarded : runWGPrefix (allocationPrefix pid peer key) u b middle=(.ok ((.submit kid packets,q),c),events))
    (allocated : runWGPrefix (state (Journal.allocate packets)) q c events=(.ok ((items,t),e),prior))
    (point : CreateComposition.ReleasePoint pid items (NativeAdapter.world t e) prior v last) :
    (∃current active,Staged.Obligations.Step ledger current ∧ NestedPeer.Evidence current debts active last v) ∧
      ∃remaining,runWGPrefix (Driver.stagingObserved hooks pid) w a h=
        ((runPrefix remaining v last).1.map (fun (value,target)=>((value,target.wg),target.ambient)),
          (runPrefix remaining v last).2) := by
  obtain ⟨after,generation,path⟩:=callback_entry before selected guarded
  have steps : Staged.Obligations.Step ledger after := by
    obtain ⟨r,_,_,_,_,_,transferred,_⟩:=path.selected
    exact transferred.symm ▸ transferLocation_step _ _ _
  obtain ⟨ids,target,performed,_,assigned,account,pending,_⟩:=
    Allocation.allocate_intervals path.ready path.shape
  rw [performed] at allocated
  cases allocated
  obtain ⟨current,active,step,evidence⟩:=point.evidence pending account
  refine ⟨⟨current,active,(steps.trans assigned).trans step,evidence⟩,?_⟩
  obtain ⟨remaining,residual⟩:=point.residual
  refine ⟨remaining,?_⟩
  rw [(createPoint selected guarded performed).residual,
    CreatePoints.lower_factor,runWGPrefix,NativeAdapter.run_lower,residual]

theorem keepalive_release_from_submission
    (before : Accounted h ledger debts locals w)
    (prepared : runWGPrefix (CausalJournal.keepalivePrepare pid) w a h=(.ok ((true,u),b),middle))
    (selected : runWGPrefix (CausalJournal.selection pid) u b middle=(.ok ((some (peer,key),q),c),events))
    (guarded : runWGPrefix (allocationPrefix pid peer key) q c events=(.ok ((.submit kid packets,t),e),prior))
    (allocated : runWGPrefix (state (Journal.allocate packets)) t e prior=(.ok ((items,r),f),called))
    (point : CreateComposition.ReleasePoint pid items (NativeAdapter.world r f) called v last) :
    ∃entered,KeepaliveChange h ledger pid ⟨true,w,u,a,b⟩ entered ∧
      (∃current active,Staged.Obligations.Step entered current ∧ NestedPeer.Evidence current debts active last v) ∧
      ∃remaining,runWGPrefix (Driver.keepaliveObserved hooks pid) w a h=
        ((runPrefix remaining v last).1.map (fun (value,target)=>((value,target.wg),target.ambient)),
          (runPrefix remaining v last).2) := by
  obtain ⟨_,_,entered,account,change⟩:=keepalive_entry before prepared
  obtain ⟨evidence,remaining,original⟩:=release_from_submission account selected guarded allocated point
  exact ⟨entered,change,evidence,remaining,(keepalivePoint prepared).residual.trans original⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingComposition
