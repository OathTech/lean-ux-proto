import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixStagingCreateQuiet
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteCreateLoop

/-! The actual refusal loop certifies each free access and labelled terminal
receipt at the same exact singleton settlement, then continues on its successor. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Staging.Creation
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation Staged.Obligations QueueHandoff HandshakeSecurity.StagedConservation
open CreateDisposal CompleteCarrier
set_option maxHeartbeats 600000

theorem free_loop_cuts (reason : Terminal.Reason) (phase : TxLocalPhase) (items : List SkbId)
    (before : Accounted history ledger debts (⟨phase,pid,items⟩::locals) w.wg)
    (pending : PendingBatch history ledger items) :
    ∃ v suffix afterLedger,
      runPrefix (loop reason items) w history=(.ok ((),v),history++suffix) ∧
      Cuts CompleteProduct.Safe history suffix ∧ Staged.Obligations.Step ledger afterLedger ∧
      Accounted (history++suffix) afterLedger debts locals v.wg := by
  induction items generalizing w history ledger with
  | nil=>
    refine ⟨w,[],ledger,?_,Cuts.nil ⟨debts,.accounted _ _ _ _ before⟩,.refl _,?_⟩
    · simp [loop,runPrefix_pure]
    · simpa only [List.append_nil] using (show Accounted history ledger debts locals w.wg from
        ⟨empty_local phase before.entry,before.complete⟩)
  | cons id items ih=>
    have unique : (id::items).Nodup := (List.nodup_append.mp before.entry.inventory.localUnique).1
    have absent := (List.nodup_cons.mp unique).1
    obtain ⟨ticket,position,ordinal,generation,value,member,origin⟩ := pending id (List.mem_cons_self ..)
    obtain ⟨u,accesses,cleanup,first,cuts,step,atRest,_⟩ :=
      Disposal.labelled_total reason id phase CompleteProduct.Safe
        (fun ledger locals h w before=>⟨debts,.accounted ledger locals h w before⟩) before member origin
    let receipt : Terminal.Receipt := ⟨reason,id,⟨(),w,u⟩⟩
    let outcome := Staged.Obligations.Terminal.disposed (history++accesses).length reason
    let assigned := settle [ticket] outcome ledger
    let middle := accesses++[CausalJournal.Event.terminalDrop receipt]
    have ownedRest : Accounted (history++middle) assigned debts (⟨phase,pid,items⟩::locals) u.wg := by
      simpa only [middle,List.append_assoc] using atRest
    have rest : PendingBatch history ledger items :=
      fun other inside=>pending other (List.mem_cons_of_mem id inside)
    have remaining : PendingBatch (history++middle) assigned items :=
      (rest.settle_other before.entry.core.valid member origin absent outcome).append middle
    obtain ⟨v,suffix,afterLedger,last,later,steps,final⟩ := ih ownedRest remaining
    refine ⟨v,middle++suffix,afterLedger,?_,cuts.append later,step.trans steps,?_⟩
    · rw [loop_cons,runPrefix_bind,first]
      simpa only [middle,List.append_assoc] using last
    · simpa only [List.append_assoc] using final

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Staging.Creation
