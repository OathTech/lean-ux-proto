import Leanux.Proofs.WG.RetirementSecurity.TxCryptAllocation

/-! TX readiness excludes live encryption aliases by the actual packet
mark. Removing the selected owning queue batch therefore cannot strand an
encryption alias or permit disposal of a pending encryption packet. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem TxCryptInventory.ready_outside (crypt : TxCryptInventory active w)
    (inventory : TxInventory locals w) (found : peerAt w pid = some p)
    (queue : p.txQueue.all = items :: rest) (head : items.head? = some first)
    (ready : TxDisposition.HeadState first .dead w ∨ TxDisposition.HeadState first .crypted w) :
    CryptOutside items active w := by
  intro id inside aliased
  obtain ⟨batch,member,contains⟩ := List.mem_flatten.mp aliased
  obtain ⟨other,q,resident,queued⟩ := crypt.owners batch member
  by_cases same : pid = other
  · subst other
    have samePeer : q = p := Option.some.inj (resident.symm.trans found)
    subst q
    rw [queue] at queued
    rcases List.mem_cons.mp queued with sameBatch | remaining
    · subst batch
      obtain ⟨cryptFirst,cryptHead,packet,packetFound,mark⟩ := crypt.uncrypted items member
      have sameFirst : cryptFirst = first := Option.some.inj (cryptHead.symm.trans head)
      subst cryptFirst
      rcases ready with ⟨readyPacket,readyFound,readyMark⟩ | ⟨readyPacket,readyFound,readyMark⟩ <;>
        have samePacket := Option.some.inj (packetFound.symm.trans readyFound) <;>
        subst readyPacket <;> simp_all
    · have unique := inventory.queueUnique pid p found
      have split : txPeerItems p = items ++ rest.flatten := by simp [txPeerItems,queue]
      rw [split] at unique
      exact (List.nodup_append.mp unique).2.2 id inside id
        (List.mem_flatten.mpr ⟨batch,remaining,contains⟩) rfl
  · exact inventory.peersSeparate pid p other q found resident same id
      (by simp [txPeerItems,queue,inside]) (List.mem_flatten.mpr ⟨batch,queued,contains⟩)

theorem TxCryptInventory.drop_native (crypt : TxCryptInventory active w)
    (outside : CryptOutside items active w)
    (cached : ∀ p, peerAt w pid = some p → p.txQueue.peeked = some items)
    (a b : Ambient)
    (run : ((txDropSource pid).run w).run a = .ok (((),v),b)) :
    TxCryptInventory active v := by
  obtain ⟨d,p,device,stored,_,after⟩ := txDrop_effect pid a b run
  have found : peerAt w pid = some p := by simp [peerAt,device,stored]
  have peeked := cached p found
  have queue : p.txQueue.all = items :: p.txQueue.dropPeeked.all := by
    simp [PrevQueue.all,PrevQueue.dropPeeked,peeked]
  have ring : TxRing.nativeCell v = TxRing.nativeCell w := by
    simp [TxRing.nativeCell,after,replacePeer,device]
  have live := crypt_items_eq ring
  have packets : TxDisposition.txPackets v = TxDisposition.txPackets w := by
    funext id
    simp [TxDisposition.txPackets,after,replacePeer,device]
  refine ⟨TxDisposition.LiveFrontier.physical_transport ring crypt.physical,?_,?_,?_⟩
  · simpa only [live] using crypt.unique
  · intro batch member
    rw [live] at member
    obtain ⟨other,q,resident,queued⟩ := crypt.owners batch member
    by_cases same : pid = other
    · subst other
      have samePeer : q = p := Option.some.inj (resident.symm.trans found)
      subst q
      rw [queue] at queued
      have remaining : batch ∈ p.txQueue.dropPeeked.all := by
        rcases List.mem_cons.mp queued with selected | remaining
        · subst batch
          obtain ⟨first,head,_⟩ := crypt.uncrypted items member
          exact (outside first (List.mem_of_head? head)
            (List.mem_flatten.mpr ⟨items,member,List.mem_of_head? head⟩)).elim
        · exact remaining
      exact ⟨pid,{p with txQueue := p.txQueue.dropPeeked},
        by simp [peerAt,after,replacePeer],remaining⟩
    · refine ⟨other,q,?_,queued⟩
      simpa [peerAt,after,replacePeer,device,Std.TreeMap.getElem?_insert,same] using resident
  · simpa only [live,TxDisposition.HeadState,packets] using crypt.uncrypted

end Leanux.Proofs.WG.RetirementSecurity
