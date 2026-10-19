import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCreateDisposal
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCoverageAllocation

/-! A newly allocated native batch has pending tickets, never old cleanup
debts. This source fact is stronger than a full entry's physical coverage. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations

/-- Each returned native ID has its own freshly assigned pending ordinal. -/
theorem allocated_pending_batch (validLedger : Valid births ledger) (packets : List DataPacket)
    (valid : (run : WGRunWitness (List SkbId)).Valid (packets.mapM newTxSkb))
    (device : run.before.dev = some d)
    (aligned : Aligned related (pendingAt (.selected takePosition) ledger) packets) :
    CreateDisposal.PendingBatch (history ++ [.old (.allocated packets run)])
      (assignBatch takePosition history.length ledger) run.value := by
  have lengthEq : (pendingAt (.selected takePosition) ledger).length = packets.length := by
    generalize selected : pendingAt (.selected takePosition) ledger = tickets at aligned ⊢
    clear valid selected
    induction aligned with
    | nil => rfl
    | cons _ _ ih => simp only [List.length_cons,ih]
  obtain ⟨items,_,_,_,_,_,_⟩ := TxDisposition.ItemSeparation.allocate_result packets device valid
  intro id member
  obtain ⟨ordinal,atId⟩ := List.mem_iff_getElem?.mp member
  have bound : ordinal < (pendingAt (.selected takePosition) ledger).length := by
    have below := (List.getElem?_eq_some_iff.mp atId).1
    rw [items,List.length_range'] at below
    simpa only [lengthEq] using below
  let ticket := (pendingAt (.selected takePosition) ledger)[ordinal]
  have atTicket : (pendingAt (.selected takePosition) ledger)[ordinal]? = some ticket :=
    List.getElem?_eq_getElem bound
  obtain ⟨packet,newId,_,_,sameId,origin,_,_⟩ :=
    allocated_ticket history packets run valid device aligned atTicket
  have equal : newId = id := Option.some.inj (sameId.symm.trans atId)
  subst newId
  exact ⟨ticket,history.length,ordinal,d.ifindex,PacketMaterial.material packet,
    assignBatch_at validLedger atTicket,origin⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
