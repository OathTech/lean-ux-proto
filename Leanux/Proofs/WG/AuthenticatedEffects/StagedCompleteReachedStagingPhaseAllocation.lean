import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPhaseCreate

/-! Silent allocator prefixes are joined to the original staging invocation.
New cells are ordinal aliases of its selected tickets until the existing
batch receipt; the remaining receipt saves the original allocator entry. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Staged.Obligations CompleteCarrier AllocatedObligation Staging
set_option maxHeartbeats 600000

def allocationRemaining (pid : PeerId) (packets : List DataPacket) (count : Nat)
    (prefixItems : List SkbId) (original : WGWorld) (clock : Ambient) : WGPrefix Event Unit := do
  let suffixItems←receiptWGObserved (liftWGPrefix ((packets.drop count).mapM newTxSkb))
    (fun run=>Event.old (.allocated packets {run with value:=prefixItems++run.value,before:=original,ambientBefore:=clock}))
  CausalJournal.create pid (prefixItems++suffixItems)

/-- All finite loop cuts are reached from the actual selected caller. The
interval retains entry accounting plus exact native aliases; no idle account
is asserted in the partially allocated world. -/
theorem allocation_every_prefix
    (before : Accounted h ledger debts locals w)
    (selected : runWGPrefix (CausalJournal.selection pid) w a h=(.ok ((some (peer,key),u),b),middle))
    (guarded : runWGPrefix (allocationPrefix pid peer key) u b middle=(.ok ((.submit kid packets,v),c),last))
    (bound : count≤packets.length) :
    ∃ after generation prefixItems cut,
      Staged.Obligations.Step ledger after ∧
      Allocation.Interval last after debts locals generation pid peer h.length kid packets v c count prefixItems cut ∧
      runWGPrefix (liftWGPrefix ((packets.take count).mapM newTxSkb)) v c last=
        (.ok ((prefixItems,cut),c),last) ∧
      runWGPrefix (Driver.stagingObserved hooks pid) w a h=
        runWGPrefix (allocationRemaining pid packets count prefixItems v c) cut c last := by
  obtain ⟨after,generation,path⟩:=Staging.Points.callback_entry before selected guarded
  obtain ⟨items,q,performed,_,_,accounted,pending,intervals⟩:=Allocation.allocate_intervals path.ready path.shape
  obtain ⟨prefixItems,cut,interval,prefixRun,rest,restRun,ordered⟩:=intervals count bound
  have steps : Staged.Obligations.Step ledger after := by
    obtain ⟨r,_,_,_,_,_,transferred,_⟩:=path.selected
    rw [transferred]
    exact transferLocation_step _ _ _
  refine ⟨after,generation,prefixItems,cut,steps,interval,prefixRun,?_⟩
  rw [(Staging.Points.createPoint selected guarded performed).residual]
  unfold allocationRemaining
  rw [Staging.Points.run_bind,runWGPrefix_receiptWGObserved,runWGPrefix_lift,restRun]
  dsimp only
  rw [←ordered]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
