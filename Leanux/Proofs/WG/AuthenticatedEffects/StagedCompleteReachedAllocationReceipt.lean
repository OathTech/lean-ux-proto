import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedAllocationCarrier

/-! Connect every silent native batch cut to the actual completed allocation
receipt and its one fixed ledger assignment. The selected caller remains an
explicit entry premise; global reachability of that caller is separate. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Allocation
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations AllocatedObligation CausalJournal
open CompleteCarrier

/-- No successful-prefix hypothesis is needed: the selected native entry
has a device, and every requested fixed loop cut is reached by actual calls. -/
theorem interval_exists
    (before : CompleteSelected.Ready ledger debts locals generation pid peer position history w a)
    (shape : BatchPayload.Shape pid kid peer.staged packets) (bound : n≤packets.length) :
    ∃ items v, Interval history ledger debts locals generation pid peer position kid packets w a n items v := by
  have epoch := before.vacant.1
  cases device : w.dev with
  | none=>simp [Packets.epoch,device] at epoch
  | some d=>
    obtain ⟨items,v,path⟩ := path_total packets device bound
    exact ⟨items,v,before,shape,path⟩

/-- The same actual allocator return supplies both its receipt-level ledger
and every intermediate native world. At intermediate cuts the journal and
ticket assignment are unchanged; only the explicit prefix aliases exist. -/
theorem allocate_intervals
    (before : CompleteSelected.Ready ledger debts locals generation pid peer position history w a)
    (shape : BatchPayload.Shape pid kid peer.staged packets) :
    ∃ (allItems : List SkbId) (last : WGWorld),
      let receipt : WGRunWitness (List SkbId) := ⟨allItems,w,last,a,a⟩
      let events := history++[Event.old (.allocated packets receipt)]
      let after := assignBatch position history.length ledger
      runWGPrefix (state (Journal.allocate packets)) w a history=(.ok ((allItems,last),a),events) ∧
      receipt.Valid (packets.mapM newTxSkb) ∧ Staged.Obligations.Step ledger after ∧
      Accounted events after debts (⟨.unpublished,pid,allItems⟩::locals) last ∧
      CreateDisposal.PendingBatch events after allItems ∧
      ∀ n, n≤packets.length → ∃ items cut,
        Interval history ledger debts locals generation pid peer position kid packets w a n items cut ∧
        runWGPrefix (liftWGPrefix ((packets.take n).mapM newTxSkb)) w a history=
          (.ok ((items,cut),a),history) ∧
        ∃ rest, (((packets.drop n).mapM newTxSkb).run cut).run a=.ok ((rest,last),a) ∧
          allItems=items++rest := by
  obtain ⟨allItems,last,performed,native,step,accounted,pending⟩ := CompleteSelected.allocate before shape
  refine ⟨allItems,last,performed,native,step,accounted,pending,?_⟩
  intro n bound
  obtain ⟨items,cut,interval⟩ := interval_exists before shape bound
  exact ⟨items,cut,interval,interval.path.silent history,interval.path.remaining native⟩

/-- A later caller Stop cannot retroactively remove the native allocator
return. This allocator itself is total at its actual selected entry. -/
theorem no_allocator_stop
    (before : CompleteSelected.Ready ledger debts locals generation pid peer position history w a)
    (shape : BatchPayload.Shape pid kid peer.staged packets) (reason : Stop) (lastHistory : List Event) :
    runWGPrefix (state (Journal.allocate packets)) w a history≠(.error reason,lastHistory) := by
  obtain ⟨_,_,performed,_⟩ := allocate_intervals before shape
  rw [performed]
  intro impossible
  cases impossible

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Allocation
