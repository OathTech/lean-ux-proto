import Leanux.Proofs.WG.Queues.DurableHolders
import Leanux.Proofs.WG.Queues.WorkReservations

/-! Ordered TX batch selection from the existing lasting-holder account.
The selected occurrence transfers its already funded owner to a transient loan. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.DurableHolders
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

/-- The first ledger batch for a peer, retaining the order of all other entries. -/
def TxSelected (entries : List TxHandoff) (pid : PeerId) (chosen : TxHandoff)
    (rest : List TxHandoff) : Prop :=
  ∃ before after, entries = before ++ chosen :: after ∧
    (∀ e ∈ before, e.owner.slot ≠ pid) ∧ chosen.owner.slot = pid ∧ rest = before ++ after

def withoutTx (h : DurableHolders) (rest : List TxHandoff) : DurableHolders := {h with tx := rest}

theorem TxSelected.perm (selected : TxSelected entries pid chosen rest) :
    entries.Perm (chosen :: rest) := by
  obtain ⟨before,after,rfl,_,_,rfl⟩ := selected
  exact List.perm_middle

theorem TxSelected.slot (selected : TxSelected entries pid chosen rest) : chosen.owner.slot = pid := by
  obtain ⟨_,_,_,_,slot,_⟩ := selected
  exact slot

theorem TxSelected.head {h : DurableHolders} (selected : TxSelected h.tx pid chosen rest) :
    h.items pid = chosen.item :: (h.withoutTx rest).items pid := by
  obtain ⟨before,after,split,absent,slot,rfl⟩ := selected
  have empty : before.filter (fun e => e.owner.slot == pid) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro e member
    simpa only [beq_iff_eq] using absent e member
  simp [items,withoutTx,split,List.filter_append,empty,slot]

theorem TxSelected.other {h : DurableHolders} (selected : TxSelected h.tx pid chosen rest) (q : PeerId) (ne : q ≠ pid) :
    (h.withoutTx rest).items q = h.items q := by
  obtain ⟨before,after,split,_,slot,rfl⟩ := selected
  simp [items,withoutTx,split,List.filter_append,slot,Ne.symm ne]

theorem tx_select_exists (entries : List TxHandoff) (pid : PeerId) (item : List SkbId)
    (head : ((entries.filter fun e => e.owner.slot == pid).map TxHandoff.item).head? = some item) :
    ∃ chosen rest, TxSelected entries pid chosen rest ∧ chosen.item = item := by
  induction entries with
  | nil => simp at head
  | cons first tail ih =>
    by_cases same : first.owner.slot = pid
    · have eq : first.item = item := by simpa [same] using head
      exact ⟨first,tail,⟨[],tail,rfl,by simp,same,rfl⟩,eq⟩
    · have next : ((tail.filter fun e => e.owner.slot == pid).map TxHandoff.item).head? = some item := by
        simpa [same] using head
      obtain ⟨chosen,rest,⟨before,after,split,absent,slot,rfl⟩,eq⟩ := ih next
      refine ⟨chosen,first :: (before ++ after),⟨first :: before,after,?_,?_,slot,rfl⟩,eq⟩
      · simp [split]
      · intro e member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact same
        · exact absent e member

theorem Funded.tx_selected {h : DurableHolders} (hi : h.Funded cs loans w)
    (queue : handoffTxView w pid = some batches) (head : batches.head? = some item) :
    ∃ chosen rest, TxSelected h.tx pid chosen rest ∧ chosen.item = item ∧
      ∃ p, RxCredits.resident w chosen.owner = some p ∧ p.txQueue.all.head? = some item := by
  obtain ⟨chosen,rest,selected,itemEq⟩ := tx_select_exists h.tx pid item
    (by rw [hi.aligned.tx pid batches queue] at head; exact head)
  have member : chosen.owner ∈ h.owners := by
    obtain ⟨before,after,split,_,_,_⟩ := selected
    simp [owners,split]
  obtain ⟨p,hp⟩ := hi.resident member
  obtain ⟨d,hd,_,stored,_⟩ := resident_fields hp
  have found : handoffTxView w pid = some p.txQueue.all := by
    simp [handoffTxView,hd,←selected.slot,stored]
  have eq : p.txQueue.all = batches := Option.some.inj (found.symm.trans queue)
  exact ⟨chosen,rest,selected,itemEq,p,hp,eq ▸ head⟩

theorem Funded.tx_input {h : DurableHolders} (hi : h.Funded cs loans w)
    (stable : StableRx cs w) (selected : TxSelected h.tx pid chosen rest) :
    ClearWork.Inv cs (chosen.owner :: ((h.withoutTx rest).owners ++ loans)) w := by
  refine ⟨WorkReservations.carrier_loans_perm hi.carriers ?_,stable⟩
  apply List.perm_iff_count.mpr
  intro o
  have count := List.Perm.count_eq (selected.perm.map TxHandoff.owner) o
  simp only [List.map_cons,List.count_cons] at count
  simp only [owners,withoutTx,List.count_append,List.count_cons]
  omega

end Leanux.Proofs.WG.Queues.RxCredits.DurableHolders
