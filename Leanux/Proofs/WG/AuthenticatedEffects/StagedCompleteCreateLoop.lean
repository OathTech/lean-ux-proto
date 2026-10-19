import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteCreateFree

/-! The real refusal free loop transports paired accounting on the same
ledger. Each actual labelled free supplies its singleton converse and restores
the original debts; native ownership still discharges each free operation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteCreate
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation
open Staged.Obligations QueueHandoff HandshakeSecurity.StagedConservation
open CreateDisposal CompleteCarrier
set_option pp.structureInstances false
set_option maxHeartbeats 600000

/-- Every member of an owned pending refusal batch reaches its exact labelled
free, preserving Entry and receipt completeness on the same ledger. The native
loop is total and returns the caller's exact original debts and locals. -/
theorem free_loop (reason : Terminal.Reason) (phase : TxLocalPhase) (items : List SkbId)
    (before : Accounted history ledger debts (⟨phase,pid,items⟩ :: locals) w.wg)
    (pending : PendingBatch history ledger items) :
    ∃ v suffix afterLedger,
      runPrefix (loop reason items) w history = (.ok ((),v),history ++ suffix) ∧
      Staged.Obligations.Step ledger afterLedger ∧
      Accounted (history ++ suffix) afterLedger debts locals v.wg ∧
      AllDropped (history ++ suffix) afterLedger reason items := by
  induction items generalizing w history ledger with
  | nil =>
    refine ⟨w,[],ledger,?_,.refl _,?_,?_⟩
    · simp [loop,runPrefix_pure]
    · simpa only [List.append_nil] using (show Accounted history ledger debts locals w.wg from
        ⟨empty_local phase before.entry,before.complete⟩)
    · intro id member
      cases member
  | cons id items ih =>
    have unique : (id :: items).Nodup := (List.nodup_append.mp before.entry.inventory.localUnique).1
    have absent := (List.nodup_cons.mp unique).1
    obtain ⟨ticket,position,ordinal,generation,value,member,origin⟩ := pending id (List.mem_cons_self ..)
    have selected := (before.entry.core.physical.resident ticket position ordinal member).at_origin origin
    obtain ⟨u,accesses,cleanup⟩ := cleanup_total selected.2 history
    let receipt : Terminal.Receipt := ⟨reason,id,⟨(),w,u⟩⟩
    let outcome := Staged.Obligations.Terminal.disposed (history ++ accesses).length reason
    let assigned := settle [ticket] outcome ledger
    let middle := accesses ++ [CausalJournal.Event.terminalDrop receipt]
    obtain ⟨first,step,atRest,terminal⟩ := labelled_free reason id phase cleanup before member origin
    have ownedRest : Accounted (history ++ middle) assigned debts
        (⟨phase,pid,items⟩ :: locals) u.wg := by
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
    obtain ⟨v,suffix,afterLedger,last,steps,final,done⟩ := ih ownedRest remaining
    refine ⟨v,middle ++ suffix,afterLedger,?_,step.trans steps,?_,?_⟩
    · rw [loop_cons,runPrefix_bind,first]
      simpa only [middle,List.append_assoc] using last
    · simpa only [List.append_assoc] using final
    · intro other inside
      rcases List.mem_cons.mp inside with same | later
      · subst other
        simpa only [List.append_assoc] using dropped.transport suffix steps
      · simpa only [List.append_assoc] using done other later

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteCreate
