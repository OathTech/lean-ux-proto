import Leanux.Proofs.WG.RetirementSecurity.TxOccurrences

/-! Moving a concrete batch between a native peer queue and an explicit
caller local is a permutation of physical occurrences. This proof transports
every packet's uniqueness and residency; it does not create a key credit. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

theorem TxInventory.exchange (inventory : TxInventory locals w)
    (device : w.dev = some d) (found : d.peers[pid]? = some p) (q : Peer)
    (transfer : (txLocalItems locals ++ txPeerItems p).Perm
      (txLocalItems locals' ++ txPeerItems q)) :
    TxInventory locals' (replacePeer w d pid q) := by
  have selected : peerAt w pid = some p := by simp [peerAt,device,found]
  have unique := transfer.nodup_iff.mp (inventory.combined_unique selected)
  have casesPeer : ∀ other r, peerAt (replacePeer w d pid q) other = some r →
      (other = pid ∧ r = q) ∨ (other ≠ pid ∧ peerAt w other = some r) := by
    intro other r resident
    by_cases same : pid = other
    · subst other
      exact Or.inl ⟨rfl,by simpa [peerAt,replacePeer] using resident.symm⟩
    · exact Or.inr ⟨Ne.symm same,by
        simpa [peerAt,replacePeer,device,Std.TreeMap.getElem?_insert,same] using resident⟩
  have packets : Queues.TxDisposition.txPackets (replacePeer w d pid q) =
      Queues.TxDisposition.txPackets w := by
    funext id
    simp [Queues.TxDisposition.txPackets,replacePeer,device]
  refine ⟨(List.nodup_append.mp unique).1,?_,?_,?_,?_,?_⟩
  · intro other r resident
    rcases casesPeer other r resident with ⟨rfl,rfl⟩ | ⟨_,old⟩
    · exact (List.nodup_append.mp unique).2.1
    · exact inventory.queueUnique other r old
  · intro left l right r leftFound rightFound different id leftMember rightMember
    rcases casesPeer left l leftFound with ⟨rfl,rfl⟩ | ⟨leftDifferent,leftOld⟩
    · rcases casesPeer right r rightFound with ⟨rfl,rfl⟩ | ⟨_,rightOld⟩
      · exact different rfl
      · exact inventory.combined_separate selected rightOld different
          (transfer.mem_iff.mpr (List.mem_append_right _ leftMember)) rightMember
    · rcases casesPeer right r rightFound with ⟨rfl,rfl⟩ | ⟨_,rightOld⟩
      · exact inventory.combined_separate selected leftOld (Ne.symm leftDifferent)
          (transfer.mem_iff.mpr (List.mem_append_right _ rightMember)) leftMember
      · exact inventory.peersSeparate left l right r leftOld rightOld different id leftMember rightMember
  · intro other r resident id held queued
    rcases casesPeer other r resident with ⟨rfl,rfl⟩ | ⟨different,old⟩
    · exact (List.nodup_append.mp unique).2.2 id held id queued rfl
    · exact inventory.combined_separate selected old (Ne.symm different)
        (transfer.mem_iff.mpr (List.mem_append_left _ held)) queued
  · intro id member
    rw [packets]
    exact inventory.combined_resident selected
      (transfer.mem_iff.mpr (List.mem_append_left _ member))
  · intro other r resident id member
    rw [packets]
    rcases casesPeer other r resident with ⟨rfl,rfl⟩ | ⟨_,old⟩
    · exact inventory.combined_resident selected
        (transfer.mem_iff.mpr (List.mem_append_right _ member))
    · exact inventory.queueResident other r old id member

theorem TxInventory.enqueue (inventory : TxInventory (⟨.unpublished,pid,items⟩ :: locals) w)
    (device : w.dev = some d) (found : d.peers[pid]? = some p) :
    TxInventory locals (replacePeer w d pid {p with txQueue := p.txQueue.enqueue items}) := by
  apply inventory.exchange device found
  apply List.perm_iff_count.mpr
  intro id
  simp [txLocalItems,txPeerItems,Queues.prev_enqueue_all,List.flatten_append,List.count_append]
  omega

theorem TxInventory.drop (inventory : TxInventory locals w)
    (device : w.dev = some d) (found : d.peers[pid]? = some p)
    (peeked : p.txQueue.peeked = some items) :
    TxInventory (⟨.selected,pid,items⟩ :: locals)
      (replacePeer w d pid {p with txQueue := p.txQueue.dropPeeked}) := by
  apply inventory.exchange device found
  apply List.perm_iff_count.mpr
  intro id
  simp [txLocalItems,txPeerItems,PrevQueue.all,PrevQueue.dropPeeked,peeked,List.count_append]
  omega

theorem TxInventory.drop_native (inventory : TxInventory locals w)
    (cached : ∀ p, peerAt w pid = some p → p.txQueue.peeked = some items)
    (a b : Ambient)
    (run : ((txDropSource pid).run w).run a = .ok (((),v),b)) :
    TxInventory (⟨.selected,pid,items⟩ :: locals) v := by
  obtain ⟨d,p,device,found,_,after⟩ := txDrop_effect pid a b run
  rw [after]
  exact inventory.drop device found (cached p (by simp [peerAt,device,found]))

end Leanux.Proofs.WG.RetirementSecurity
