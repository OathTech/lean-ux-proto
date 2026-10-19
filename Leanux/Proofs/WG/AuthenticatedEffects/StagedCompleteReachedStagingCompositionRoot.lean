import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingCompositionSelected
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPrimitiveExecutions

/-! Rooted child contracts retain actual keepalive admission and product-world
writeback. Allocation aliases and CreatePhase remain the existing concrete
child families; no universal child certificate is inferred from endpoint Covers. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingComposition
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Staged.Obligations CompleteCarrier Staging Staging.Points StagingPhase StagingPrimitive
set_option maxHeartbeats 600000

theorem keepalive_repayment_from_rejection
    (before : Accounted h ledger debts locals w)
    (prepared : runWGPrefix (CausalJournal.keepalivePrepare pid) w a h=(.ok ((true,u),b),middle))
    (selected : runWGPrefix (CausalJournal.selection pid) u b middle=(.ok ((some (peer,key),q),c),events))
    (guarded : runWGPrefix (allocationPrefix pid peer key) q c events=(.ok ((.rejected rejectedKey invalid,t),e),prior))
    (call : Call (rejectPrefixShape peer.staged rejectedKey invalid) t e prior (.repayment repayKey) r f called context)
    (point : KeyPoint (StagingPrimitive.keyShape repayKey) r f leaf v d rest) :
    ∃ entered after generation,
      KeepaliveChange h ledger pid ⟨true,w,u,a,b⟩ entered ∧
      Staged.Obligations.Step entered after ∧
      CompleteSelected.Ready after debts locals generation pid peer middle.length called v d ∧
      runWGPrefix (Driver.keepaliveObserved hooks pid) w a h=
        runWGPrefix (context (liftWGPrefix rest) >>= fun _=>rejectedTail pid peer) v d called := by
  obtain ⟨_,_,entered,account,change⟩:=keepalive_entry before prepared
  obtain ⟨after,generation,steps,ready,original⟩:=repayment_from_rejection account selected guarded call point
  exact ⟨entered,after,generation,change,steps,ready,(keepalivePoint prepared).residual.trans original⟩

/-- This is only the writeback consequence of an already rooted native
residual. The concrete callers below supply its fixed source provenance. -/
theorem lift_residual {action rest : WGPrefix Event α} (w : World)
    (same : runWGPrefix action w.wg w.ambient h=runWGPrefix rest v b middle) :
    runPrefix (liftWGObserver action) w h=
      runPrefix (liftWGObserver rest) {w with wg:=v,ambient:=b} middle := by
  rw [liftWGObserver_run,liftWGObserver_run,same]

theorem reserve_product_from_selection (w : World)
    (before : Accounted h ledger debts locals w.wg)
    (selected : runWGPrefix (CausalJournal.selection pid) w.wg w.ambient h=(.ok ((some (peer,key),u),b),middle))
    (call : Call (allocationPrefixShape pid peer key) u b middle (.reserve slot) q c events context)
    (point : ReservePoint slot q c events v d last rest) :
    ∃ after generation,Staged.Obligations.Step ledger after ∧
      CompleteSelected.Ready after debts locals generation pid peer h.length last v d ∧
      runPrefix (liftWGObserver (Driver.stagingObserved hooks pid)) w h=
        runPrefix (liftWGObserver (context rest >>= allocationTail pid peer)) {w with wg:=v,ambient:=d} last := by
  obtain ⟨after,generation,steps,ready,run⟩:=reserve_from_selection before selected call point
  exact ⟨after,generation,steps,ready,lift_residual w run⟩

theorem repayment_product_from_rejection (w : World)
    (before : Accounted h ledger debts locals w.wg)
    (selected : runWGPrefix (CausalJournal.selection pid) w.wg w.ambient h=(.ok ((some (peer,key),u),b),middle))
    (guarded : runWGPrefix (allocationPrefix pid peer key) u b middle=(.ok ((.rejected rejectedKey invalid,q),c),events))
    (call : Call (rejectPrefixShape peer.staged rejectedKey invalid) q c events (.repayment repayKey) t e prior context)
    (point : KeyPoint (StagingPrimitive.keyShape repayKey) t e leaf v d rest) :
    ∃ after generation,Staged.Obligations.Step ledger after ∧
      CompleteSelected.Ready after debts locals generation pid peer h.length prior v d ∧
      runPrefix (liftWGObserver (Driver.stagingObserved hooks pid)) w h=
        runPrefix (liftWGObserver (context (liftWGPrefix rest) >>= fun _=>rejectedTail pid peer))
          {w with wg:=v,ambient:=d} prior := by
  obtain ⟨after,generation,steps,ready,run⟩:=repayment_from_rejection before selected guarded call point
  exact ⟨after,generation,steps,ready,lift_residual w run⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingComposition
