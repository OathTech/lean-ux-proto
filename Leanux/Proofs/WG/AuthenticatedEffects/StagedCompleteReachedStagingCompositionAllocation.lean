import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingCompositionCreation
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedAllocationContinuation

/-! Actual staging submission derives each allocator alias interval and
its original continuation. The physical prefix is tied to the selected
cohort; its cells are not treated as new admissions or already receipted. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingComposition
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Staged.Obligations CompleteCarrier Staging Staging.Points StagingPhase
set_option maxHeartbeats 600000

theorem allocation_from_submission
    (before : Accounted h ledger debts locals w)
    (selected : runWGPrefix (CausalJournal.selection pid) w a h=(.ok ((some (peer,key),u),b),middle))
    (guarded : runWGPrefix (allocationPrefix pid peer key) u b middle=(.ok ((.submit kid packets,q),c),events))
    (path : Allocation.Path packets q c count items v) :
    ∃ after generation,Staged.Obligations.Step ledger after ∧
      Allocation.Interval events after debts locals generation pid peer h.length kid packets q c count items v ∧
      runWGPrefix (Driver.stagingObserved hooks pid) w a h=
        runWGPrefix (Allocation.remainder packets count items q c >>= CausalJournal.create pid) v c events := by
  obtain ⟨after,generation,callback⟩:=callback_entry before selected guarded
  have steps : Staged.Obligations.Step ledger after := by
    obtain ⟨r,_,_,_,_,_,transferred,_⟩:=callback.selected
    exact transferred.symm ▸ transferLocation_step _ _ _
  let interval : Allocation.Interval events after debts locals generation pid peer h.length kid packets q c count items v :=
    ⟨callback.ready,callback.shape,path⟩
  refine ⟨after,generation,steps,interval,?_⟩
  rw [callback.continuation]
  change runWGPrefix (state (Journal.allocate packets) >>= CausalJournal.create pid) q c events=_
  rw [run_bind,run_bind,interval.residual]

theorem keepalive_allocation_from_submission
    (before : Accounted h ledger debts locals w)
    (prepared : runWGPrefix (CausalJournal.keepalivePrepare pid) w a h=(.ok ((true,u),b),middle))
    (selected : runWGPrefix (CausalJournal.selection pid) u b middle=(.ok ((some (peer,key),q),c),events))
    (guarded : runWGPrefix (allocationPrefix pid peer key) q c events=(.ok ((.submit kid packets,t),e),prior))
    (path : Allocation.Path packets t e count items v) :
    ∃ entered after generation,
      KeepaliveChange h ledger pid ⟨true,w,u,a,b⟩ entered ∧
      Staged.Obligations.Step entered after ∧
      Allocation.Interval prior after debts locals generation pid peer middle.length kid packets t e count items v ∧
      runWGPrefix (Driver.keepaliveObserved hooks pid) w a h=
        runWGPrefix (Allocation.remainder packets count items t e >>= CausalJournal.create pid) v e prior := by
  obtain ⟨_,_,entered,account,change⟩:=keepalive_entry before prepared
  obtain ⟨after,generation,steps,interval,original⟩:=allocation_from_submission account selected guarded path
  exact ⟨entered,after,generation,change,steps,interval,(keepalivePoint prepared).residual.trans original⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingComposition
