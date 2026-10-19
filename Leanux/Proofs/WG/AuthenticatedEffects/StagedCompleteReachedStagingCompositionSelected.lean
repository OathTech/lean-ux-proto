import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingCompositionCalls

/-! Concrete child cuts are rooted at the actual selected source invocation.
The selected ledger and cached cohort come from the original take/borrow;
no child-entry account or whole-staging certificate is assumed. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingComposition
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Staged.Obligations CompleteCarrier Staging Staging.Points StagingPhase StagingPrimitive
set_option maxHeartbeats 600000

theorem reserve_from_selection
    (before : Accounted h ledger debts locals w)
    (selected : runWGPrefix (CausalJournal.selection pid) w a h=(.ok ((some (peer,key),u),b),middle))
    (call : Call (allocationPrefixShape pid peer key) u b middle (.reserve slot) q c events context)
    (point : ReservePoint slot q c events v d last rest) :
    ∃ after generation,Staged.Obligations.Step ledger after ∧
      CompleteSelected.Ready after debts locals generation pid peer h.length last v d ∧
      runWGPrefix (Driver.stagingObserved hooks pid) w a h=
        runWGPrefix (context rest >>= allocationTail pid peer) v d last := by
  obtain ⟨after,generation,path,ready⟩:=Staging.Points.selected_entry before selected
  obtain ⟨r,_,_,_,_,_,transferred,_⟩:=path
  have steps : Staged.Obligations.Step ledger after := transferred.symm ▸ transferLocation_step _ _ _
  have entered:=call.entry (allocation_prefix_covers key ready)
  refine ⟨after,generation,steps,point.selected entered,?_⟩
  rw [(selectedPoint selected).residual,run_bind,run_bind,call.resume point.residual]

theorem repayment_from_rejection
    (before : Accounted h ledger debts locals w)
    (selected : runWGPrefix (CausalJournal.selection pid) w a h=(.ok ((some (peer,key),u),b),middle))
    (guarded : runWGPrefix (allocationPrefix pid peer key) u b middle=(.ok ((.rejected rejectedKey invalid,q),c),events))
    (call : Call (rejectPrefixShape peer.staged rejectedKey invalid) q c events (.repayment repayKey) t e prior context)
    (point : KeyPoint (keyShape repayKey) t e leaf v d rest) :
    ∃ after generation,Staged.Obligations.Step ledger after ∧
      CompleteSelected.Ready after debts locals generation pid peer h.length prior v d ∧
      runWGPrefix (Driver.stagingObserved hooks pid) w a h=
        runWGPrefix (context (liftWGPrefix rest) >>= fun _=>rejectedTail pid peer) v d prior := by
  obtain ⟨after,generation,path⟩:=callback_entry before selected guarded
  have steps : Staged.Obligations.Step ledger after := by
    obtain ⟨r,_,_,_,_,_,transferred,_⟩:=path.selected
    exact transferred.symm ▸ transferLocation_step _ _ _
  have entered:=call.entry (reject_prefix_covers peer.staged rejectedKey invalid path.ready)
  obtain ⟨atPoint,child⟩:=repayment_every_point entered point
  refine ⟨after,generation,steps,atPoint,?_⟩
  have original := (callbackPoint selected guarded).residual
  change runWGPrefix (Driver.stagingObserved hooks pid) w a h=
    runWGPrefix (HeldSource.noKey pid peer rejectedKey invalid) q c events at original
  rw [rejection_factor] at original
  rw [original,run_bind,run_bind,call.resume child]

theorem keepalive_reserve_from_selection
    (before : Accounted h ledger debts locals w)
    (prepared : runWGPrefix (CausalJournal.keepalivePrepare pid) w a h=(.ok ((true,u),b),middle))
    (selected : runWGPrefix (CausalJournal.selection pid) u b middle=(.ok ((some (peer,key),q),c),events))
    (call : Call (allocationPrefixShape pid peer key) q c events (.reserve slot) t e prior context)
    (point : ReservePoint slot t e prior v d last rest) :
    ∃ entered after generation,
      KeepaliveChange h ledger pid ⟨true,w,u,a,b⟩ entered ∧
      Staged.Obligations.Step entered after ∧
      CompleteSelected.Ready after debts locals generation pid peer middle.length last v d ∧
      runWGPrefix (Driver.keepaliveObserved hooks pid) w a h=
        runWGPrefix (context rest >>= allocationTail pid peer) v d last := by
  obtain ⟨_,_,entered,account,change⟩:=keepalive_entry before prepared
  obtain ⟨after,generation,steps,ready,original⟩:=reserve_from_selection account selected call point
  exact ⟨entered,after,generation,change,steps,ready,(keepalivePoint prepared).residual.trans original⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingComposition
