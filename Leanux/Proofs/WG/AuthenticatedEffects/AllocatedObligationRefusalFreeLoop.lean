import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationRefusalEntryFrames

/-! The real refusal free loop consumes the same explicit owned batch. Each
iteration retains the full entry and its actual labelled receipt; the loop
is total because native ownership and pending backing discharge each free. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateDisposal
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations QueueHandoff HandshakeSecurity.StagedConservation
set_option pp.structureInstances false
set_option maxHeartbeats 600000

/-- Every member of an owned pending refusal batch is freed exactly along
the original source loop, with full canonical entry and immutable named
terminal evidence for the same tickets. No completed enclosing caller or
free-success premise is required. -/
theorem loop_entry_total (reason : Terminal.Reason) (phase : TxLocalPhase) (items : List SkbId)
    (before : StagedEntry.Inv history ledger debts (⟨phase,pid,items⟩ :: locals) w.wg)
    (pending : PendingBatch history ledger items) :
    ∃ v suffix afterLedger afterDebts,
      runPrefix (loop reason items) w history = (.ok ((),v),history ++ suffix) ∧
      Staged.Obligations.Step ledger afterLedger ∧
      StagedEntry.Inv (history ++ suffix) afterLedger afterDebts locals v.wg ∧
      AllDropped (history ++ suffix) afterLedger reason items := by
  induction items generalizing w history ledger debts with
  | nil =>
    refine ⟨w,[],ledger,debts,?_,.refl _,?_,?_⟩
    · simp [loop,runPrefix_pure]
    · simpa only [List.append_nil] using empty_local phase before
    · intro id member
      cases member
  | cons id items ih =>
    have unique : (id :: items).Nodup := (List.nodup_append.mp before.inventory.localUnique).1
    have absent := (List.nodup_cons.mp unique).1
    obtain ⟨ticket,position,ordinal,generation,value,member,origin⟩ := pending id (List.mem_cons_self ..)
    have selected := (before.core.physical.resident ticket position ordinal member).at_origin origin
    obtain ⟨u,accesses,cleanup⟩ := cleanup_total selected.2 history
    let receipt : Terminal.Receipt := ⟨reason,id,⟨(),w,u⟩⟩
    let outcome := Staged.Obligations.Terminal.disposed (history ++ accesses).length reason
    let assigned := settle [ticket] outcome ledger
    let assignedDebts := forgetFreedCell (history ++ accesses) generation id
      (⟨ticket,position,ordinal,outcome⟩ :: debts)
    let middle := accesses ++ [CausalJournal.Event.terminalDrop receipt]
    obtain ⟨first,step,atRest,terminal⟩ := labelled_free_entry reason id phase cleanup before member origin
    have ownedRest : StagedEntry.Inv (history ++ middle) assigned assignedDebts
        (⟨phase,pid,items⟩ :: locals) u.wg := by
      simpa only [middle,List.append_assoc] using atRest
    have rest : PendingBatch history ledger items :=
      fun other inside => pending other (List.mem_cons_of_mem id inside)
    have remaining : PendingBatch (history ++ middle) assigned items :=
      (rest.settle_other before.core.valid member origin absent outcome).append middle
    have dropped : Dropped (history ++ middle) assigned reason id := by
      refine ⟨ticket,position,ordinal,generation,value,(history ++ accesses).length,receipt,
        origin.append middle,?_,?_,rfl,rfl,terminal⟩
      · simp only [middle,←List.append_assoc,List.getElem?_concat_length]
      · exact (FirstTerminal.labelled_cut reason id w u history accesses cleanup).1
    obtain ⟨v,suffix,afterLedger,afterDebts,last,steps,final,done⟩ := ih ownedRest remaining
    refine ⟨v,middle ++ suffix,afterLedger,afterDebts,?_,step.trans steps,?_,?_⟩
    · rw [loop_cons,runPrefix_bind,first]
      simpa only [middle,List.append_assoc] using last
    · simpa only [List.append_assoc] using final
    · intro other inside
      rcases List.mem_cons.mp inside with same | later
      · subst other
        simpa only [List.append_assoc] using dropped.transport suffix steps
      · simpa only [List.append_assoc] using done other later

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateDisposal
