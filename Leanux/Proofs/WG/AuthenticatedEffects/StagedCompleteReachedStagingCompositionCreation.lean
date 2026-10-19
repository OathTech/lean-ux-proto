import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingCompositionQueued
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreatePhaseCoverage

/-! Creation's fixed source points are reached by the actual selection,
guard and allocation runs. Their unpublished cohort and ledger assignment
are derived at that boundary, and the original staging continuation is kept.
The adapter exposes only the actual WG/ambient projection. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingComposition
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Staged.Obligations CompleteCarrier Staging Staging.Points StagingPhase
set_option maxHeartbeats 600000

theorem create_live_rebase (steps : Staged.Obligations.Step root current)
    (live : CreatePhase.Live current debts locals pid items h w) :
    CreatePhase.Live root debts locals pid items h w := by
  cases live with
  | unpublished next later pending account=>exact .unpublished next (steps.trans later) pending account
  | queued next later pending account=>exact .queued next (steps.trans later) pending account
  | cleanup next later reason done remaining ordered settled pending account=>
    exact .cleanup next (steps.trans later) reason done remaining ordered settled pending account
  | disposed next later reason settled account=>exact .disposed next (steps.trans later) reason settled account

/-- Actual submission supplies every fixed creation point with the same
original ticket lineage and its source continuation, even before later Stop.
Creation's deeper primitive children retain their separate obligations. -/
theorem create_from_submission
    (before : Accounted h ledger debts locals w)
    (selected : runWGPrefix (CausalJournal.selection pid) w a h=(.ok ((some (peer,key),u),b),middle))
    (guarded : runWGPrefix (allocationPrefix pid peer key) u b middle=(.ok ((.submit kid packets,q),c),events))
    (allocated : runWGPrefix (state (Journal.allocate packets)) q c events=(.ok ((items,t),e),prior))
    (point : CreatePoints.Point (CreatePoints.createShape pid items) (NativeAdapter.world t e) prior
      leaf v last remaining) :
    CreatePhase.Live ledger debts locals pid items last v.wg ∧
      runWGPrefix (Driver.stagingObserved hooks pid) w a h=
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
  have live:=(CreatePhase.create_covers pending account).point point
  exact ⟨create_live_rebase (steps.trans assigned) live,
    (createPoint selected guarded performed).residual.trans point.lowered⟩

/-- Keepalive preparation contributes its actual admission change before
the same staged selection and creation path. No fresh idle ledger is chosen. -/
theorem keepalive_create_from_submission
    (before : Accounted h ledger debts locals w)
    (prepared : runWGPrefix (CausalJournal.keepalivePrepare pid) w a h=(.ok ((true,u),b),middle))
    (selected : runWGPrefix (CausalJournal.selection pid) u b middle=(.ok ((some (peer,key),q),c),events))
    (guarded : runWGPrefix (allocationPrefix pid peer key) q c events=(.ok ((.submit kid packets,t),e),prior))
    (allocated : runWGPrefix (state (Journal.allocate packets)) t e prior=(.ok ((items,r),f),called))
    (point : CreatePoints.Point (CreatePoints.createShape pid items) (NativeAdapter.world r f) called
      leaf v last remaining) :
    ∃ entered,KeepaliveChange h ledger pid ⟨true,w,u,a,b⟩ entered ∧
      CreatePhase.Live entered debts locals pid items last v.wg ∧
      runWGPrefix (Driver.keepaliveObserved hooks pid) w a h=
        ((runPrefix remaining v last).1.map (fun (value,target)=>((value,target.wg),target.ambient)),
          (runPrefix remaining v last).2) := by
  obtain ⟨_,_,entered,account,change⟩:=keepalive_entry before prepared
  obtain ⟨live,original⟩:=create_from_submission account selected guarded allocated point
  exact ⟨entered,change,live,(keepalivePoint prepared).residual.trans original⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingComposition
