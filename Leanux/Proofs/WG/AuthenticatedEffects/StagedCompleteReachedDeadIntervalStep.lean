import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDeadIntervalSource

/-! Native selected ownership supplies total cleanup. The same pending
ticket is settled at the actual receipt; all remaining selected tickets stay
pending and backed, so the next original iteration has its own source entry. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.DeadIntervals
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation CreateDisposal HandshakeSecurity.StagedConservation

theorem iteration_total (reason : Terminal.Reason) (id : SkbId)
    (before : Accounted history ledger debts (⟨.selected,pid,id :: items⟩ :: locals) w.wg)
    (pending : PendingBatch history ledger (id :: items)) :
    ∃ v last after, Iteration reason pid debts locals id items w history ledger v last after := by
  have unique : (id :: items).Nodup := (List.nodup_append.mp before.entry.inventory.localUnique).1
  have absent := (List.nodup_cons.mp unique).1
  obtain ⟨ticket,position,ordinal,generation,value,member,origin⟩ := pending id (List.mem_cons_self ..)
  have selected := (before.entry.core.physical.resident ticket position ordinal member).at_origin origin
  obtain ⟨u,accesses,cleanup⟩ := cleanup_total selected.2 history
  let receipt : Terminal.Receipt := ⟨reason,id,⟨(),w,u⟩⟩
  let outcome := Staged.Obligations.Terminal.disposed (history ++ accesses).length reason
  let assigned := settle [ticket] outcome ledger
  let middle := accesses ++ [CausalJournal.Event.terminalDrop receipt]
  obtain ⟨first,step,atRest,terminal⟩ := CompleteCreate.labelled_free reason id .selected cleanup before member origin
  have ownedRest : Accounted (history ++ middle) assigned debts
      (⟨.selected,pid,items⟩ :: locals) u.wg := by
    simpa only [middle,List.append_assoc] using atRest
  have rest : PendingBatch history ledger items :=
    fun other inside => pending other (List.mem_cons_of_mem id inside)
  have remaining : PendingBatch (history ++ middle) assigned items :=
    (rest.settle_other before.entry.core.valid member origin absent outcome).append middle
  have dropped : Dropped (history ++ middle) assigned reason id := by
    refine ⟨ticket,position,ordinal,generation,value,(history ++ accesses).length,receipt,
      origin.append middle,?_,?_,rfl,rfl,terminal⟩
    · simp only [middle,←List.append_assoc,List.getElem?_concat_length]
    · exact (FirstTerminal.labelled_cut reason id w u history accesses cleanup).1
  refine ⟨u,history ++ middle,assigned,.receipt ticket position ordinal generation value accesses
    before pending member origin cleanup ?_ ?_ rfl step ownedRest remaining dropped⟩
  · simpa only [middle,List.append_assoc] using first
  · simp only [middle,receipt,List.append_assoc]

theorem Iteration.entry {id : SkbId}
    (cut : Iteration reason pid debts locals id items w history ledger v last after) :
    Accounted history ledger debts (⟨.selected,pid,id :: items⟩ :: locals) w.wg := by
  cases cut with
  | receipt _ _ _ _ _ _ initial => exact initial

theorem Iteration.pending {id : SkbId}
    (cut : Iteration reason pid debts locals id items w history ledger v last after) :
    PendingBatch history ledger (id :: items) := by
  cases cut with
  | receipt _ _ _ _ _ _ _ batch => exact batch

theorem Iteration.result {id : SkbId}
    (cut : Iteration reason pid debts locals id items w history ledger v last after) :
    Staged.Obligations.Step ledger after ∧
      Accounted last after debts (⟨.selected,pid,items⟩ :: locals) v.wg ∧
      PendingBatch last after items ∧ Dropped last after reason id := by
  cases cut with
  | receipt _ _ _ _ _ _ _ _ _ _ _ _ _ _ step accounted rest dropped => exact ⟨step,accounted,rest,dropped⟩

theorem Iteration.run {id : SkbId}
    (cut : Iteration reason pid debts locals id items w history ledger v last after) :
    runPrefix (free reason id) w history = (.ok ((),v),last) := by
  cases cut with
  | receipt _ _ _ _ _ _ _ _ _ _ _ performed => exact performed

theorem Iteration.append {id : SkbId}
    (cut : Iteration reason pid debts locals id items w history ledger v last after) :
    ∃ suffix, last = history ++ suffix := by
  cases cut with
  | receipt ticket position ordinal generation value accesses _ _ _ _ _ _ recorded =>
    exact ⟨accesses ++ [.terminalDrop ⟨reason,id,⟨(),w,v⟩⟩],by simpa only [List.append_assoc] using recorded⟩

/-- The next ledger is the singleton settlement of the same allocation
ticket, at the actual receipt appended after its original cleanup run. -/
theorem Iteration.settlement {id : SkbId}
    (cut : Iteration reason pid debts locals id items w history ledger v last after) :
    ∃ ticket position ordinal generation value accesses,
      (ticket,Status.pending (.allocated position ordinal)) ∈ ledger ∧
      Origin history position ordinal generation id value ∧
      runPrefix (FirstTerminal.cleanupFree id) w history = (.ok ((),v),history ++ accesses) ∧
      last = history ++ accesses ++ [.terminalDrop ⟨reason,id,⟨(),w,v⟩⟩] ∧
      after = settle [ticket] (.disposed (history ++ accesses).length reason) ledger ∧
      (show Terminal.Receipt from ⟨reason,id,⟨(),w,v⟩⟩).Valid := by
  cases cut with
  | receipt ticket position ordinal generation value accesses initial batch member origin cleanup performed recorded assigned =>
    exact ⟨ticket,position,ordinal,generation,value,accesses,member,origin,cleanup,recorded,assigned,
      (FirstTerminal.labelled_cut reason id w v history accesses cleanup).1⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.DeadIntervals
