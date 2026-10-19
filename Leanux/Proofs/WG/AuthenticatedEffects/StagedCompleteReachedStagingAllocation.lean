import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingCaller

/-! The concrete staging prefix supplies the allocator's selected entry and
ordered packet shape. Its original create continuation follows the same
batch receipt and ledger assignment; a later failure does not remove the
literal successful prefix or the intervening native allocation worlds. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Staging
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Obligations CausalJournal CompleteCarrier AllocatedObligation

/-- Derive allocator intervals from a source-selected callback path. The
outer staging outcome is exactly the actual create continuation, which may
Stop. No completed whole-staging run or new Ready/Shape premise is imposed. -/
theorem CallbackPath.allocation {selectedLedger : Ledger}
    (path : CallbackPath history ledger debts locals pid w a peer keypair selectedHistory
      selectedWorld selectedClock selectedLedger generation (.submit kid packets) h v b) :
    ∃ (items : List SkbId) (last : WGWorld),
      let receipt : WGRunWitness (List SkbId):=⟨items,v,last,b,b⟩
      let events:=h++[Event.old (.allocated packets receipt)]
      let after:=assignBatch history.length h.length selectedLedger
      runWGPrefix (stagingPrefix pid) w a history=(.ok ((some (peer,.submit kid packets),v),b),h) ∧
      runWGPrefix (Driver.stagingObserved hooks pid) w a history=
        runWGPrefix (CausalJournal.create pid items) last b events ∧
      receipt.Valid (packets.mapM newTxSkb) ∧ Staged.Obligations.Step selectedLedger after ∧
      Accounted events after debts (⟨.unpublished,pid,items⟩::locals) last ∧
      CreateDisposal.PendingBatch events after items ∧
      ∀ n, n≤packets.length → ∃ prefixItems cut,
        Allocation.Interval h selectedLedger debts locals generation pid peer history.length kid packets v b n prefixItems cut ∧
        runWGPrefix (liftWGPrefix ((packets.take n).mapM newTxSkb)) v b h=
          (.ok ((prefixItems,cut),b),h) ∧
        ∃ rest, (((packets.drop n).mapM newTxSkb).run cut).run b=.ok ((rest,last),b) ∧
          items=prefixItems++rest := by
  obtain ⟨items,last,performed,native,step,accounted,pending,intervals⟩:=
    Allocation.allocate_intervals path.ready path.shape
  refine ⟨items,last,path.literal,?_,native,step,accounted,pending,intervals⟩
  rw [path.continuation]
  unfold allocationTail
  change runStatePrefix (_ >>= _) v b h=_
  rw [runStatePrefix_bind]
  change runStatePrefix _ _ _ _=_ at performed
  rw [performed]
  rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Staging
