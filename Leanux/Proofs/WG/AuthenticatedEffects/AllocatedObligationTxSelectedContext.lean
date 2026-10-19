import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationTxSelectionObserved
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionIndexed

/-! The completion context is constructed from the actual selected pending
batch, retaining its exact allocation position and ordinal for every cell. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.TxSelection
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations CreateDisposal CompletionBatch

private theorem bindings_of_pending (pending : PendingBatch history ledger items) :
    ∃ bindings : List Binding, bindings.map Binding.skb = items ∧
      ∀ binding ∈ bindings, binding.recorded history ∧ binding.pending ledger := by
  induction items with
  | nil => exact ⟨[],rfl,by simp⟩
  | cons id rest ih =>
    obtain ⟨ticket,position,ordinal,generation,value,member,origin⟩ := pending id (List.mem_cons_self ..)
    obtain ⟨bindings,same,bound⟩ := ih (fun skb inside => pending skb (List.mem_cons_of_mem _ inside))
    refine ⟨⟨id,ticket,position,ordinal,generation,value⟩ :: bindings,?_,?_⟩
    · simp only [List.map_cons,same]
    · intro binding inside
      rcases List.mem_cons.mp inside with rfl | later
      · exact ⟨origin,member⟩
      · exact bound binding later

/-- Selected native ownership and source-derived pending tickets construct
completion's indexed context at the same ledger, debts and history. No
independent existential completion state is joined to another ledger. -/
theorem selected_context
    (before : StagedEntry.Inv history ledger debts (⟨.selected,pid,items⟩ :: locals) w.wg)
    (pending : PendingBatch history ledger items) :
    ∃ context : Context, context.pid = pid ∧ context.locals = locals ∧ context.items = items ∧
      context.initialLedger = ledger ∧ context.births = births history ∧
      Owned context (.sending context.items) history ledger debts w := by
  obtain ⟨bindings,same,bound⟩ := bindings_of_pending pending
  let context : Context := ⟨births history,ledger,bindings,locals,pid⟩
  have itemsEq : context.items = items := same
  refine ⟨context,rfl,rfl,itemsEq,rfl,rfl,?_,?_,rfl⟩
  · refine ⟨.refl _,fun binding member => (bound binding member).1,?_,?_⟩
    · exact ⟨[],rfl⟩
    · intro binding member
      refine ⟨fun _ => (bound binding member).2,?_⟩
      intro absent
      exact False.elim (absent (List.mem_map.mpr ⟨binding,member,rfl⟩))
  · simpa only [Phase.active,context,itemsEq] using before

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.TxSelection
