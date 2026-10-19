import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPointEntries

/-! The actual checked source supplies the allocator entry, original ordered
plaintext cohort and one assignment receipt. Silent allocator aliases and
the create/admission child retain the same fixed entry and continuation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Staging.Points
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Staged.Obligations CompleteCarrier AllocatedObligation
set_option maxHeartbeats 600000

noncomputable def createPoint
    (selected : runWGPrefix (CausalJournal.selection pid) w a h=(.ok ((some (peer,key),u),b),middle))
    (guarded : runWGPrefix (allocationPrefix pid peer key) u b middle=(.ok ((.submit kid packets,v),c),last))
    (allocated : runWGPrefix (state (Journal.allocate packets)) v c last=(.ok ((items,q),d),events)) :
    Point (stagingShape pid) w a h (CausalJournal.create pid items) q d events
      (CausalJournal.create pid items) := by
  unfold stagingShape
  apply Point.marked
  apply Point.cast (allocation_factor pid)
  refine .right (selectionShape pid) (chosenShape pid) selected
    (.right (allocationPrefixShape pid peer key) (tailShape pid peer) guarded ?_)
  exact .marked _ (.right (.child (.allocate packets)) (fun ids=>.child (.create pid ids))
    allocated (.entry (.child (.create pid items))))

structure Allocated (history : History) (ledger : Ledger) (debts : List CleanupDebt)
    (locals : List RetirementSecurity.TxLocalBatch) (pid : PeerId) (w : WGWorld) (a : Ambient)
    (peer : Peer) (generation : Nat) (kid : KeypairId) (packets : List DataPacket)
    (h : History) (v : WGWorld) (b : Ambient) where
  items : List SkbId
  after : WGWorld
  performed : runWGPrefix (state (Journal.allocate packets)) v b h=
    (.ok ((items,after),b),h++[.old (.allocated packets ⟨items,v,after,b,b⟩)])
  native : (⟨items,v,after,b,b⟩ : WGRunWitness (List SkbId)).Valid (packets.mapM newTxSkb)
  ready : CompleteSelected.Ready ledger debts locals generation pid peer history.length h v b
  shape : BatchPayload.Shape pid kid peer.staged packets
  accounted : Accounted (h++[.old (.allocated packets ⟨items,v,after,b,b⟩)])
    (assignBatch history.length h.length ledger) debts (⟨.unpublished,pid,items⟩::locals) after
  pending : CreateDisposal.PendingBatch (h++[.old (.allocated packets ⟨items,v,after,b,b⟩)])
    (assignBatch history.length h.length ledger) items
  intervals : ∀ n, n≤packets.length → ∃ prefixItems cut,
    Allocation.Interval h ledger debts locals generation pid peer history.length kid packets v b n prefixItems cut ∧
    runWGPrefix (liftWGPrefix ((packets.take n).mapM newTxSkb)) v b h=(.ok ((prefixItems,cut),b),h) ∧
    ∃ rest, (((packets.drop n).mapM newTxSkb).run cut).run b=.ok ((rest,after),b) ∧ items=prefixItems++rest
  continuation : runWGPrefix (Driver.stagingObserved hooks pid) w a history=
    runWGPrefix (CausalJournal.create pid items) after b
      (h++[.old (.allocated packets ⟨items,v,after,b,b⟩)])

/-- No allocator-success premise is added: Ready supplies the actual device
and the finite allocation loop is total. Create/admission remains the named
original child, including all its later normal and stopped outcomes. -/
theorem allocation_boundary
    (path : CallbackPath history original debts locals pid w a peer keypair selectedHistory
      selectedWorld selectedClock ledger generation (.submit kid packets) h v b) :
    Nonempty (Allocated history ledger debts locals pid w a peer generation kid packets h v b) := by
  obtain ⟨items,last,performed,native,_,accounted,pending,intervals⟩:=
    Allocation.allocate_intervals path.ready path.shape
  refine ⟨⟨items,last,performed,native,path.ready,path.shape,accounted,pending,intervals,?_⟩⟩
  exact (createPoint path.selectionRun path.guardRun performed).residual

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Staging.Points
