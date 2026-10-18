import Leanux.Proofs.WG.RetirementSecurity.TxOccurrenceTransfer
import Leanux.Proofs.WG.RetirementSecurity.RxPublishHolders

/-! Occurrence frames use queue contents and packet residency only.
Marking, encryption and endpoint/timer bookkeeping may change packet bytes
and other fields without manufacturing or duplicating physical occurrences. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

theorem TxInventory.transport (inventory : TxInventory locals w)
    (queues : ∀ pid p, peerAt v pid = some p →
      ∃ old, peerAt w pid = some old ∧ txPeerItems old = txPeerItems p)
    (packets : ∀ id packet, Queues.TxDisposition.txPackets w id = some packet →
      ∃ current, Queues.TxDisposition.txPackets v id = some current) : TxInventory locals v := by
  refine ⟨inventory.localUnique,?_,?_,?_,?_,?_⟩
  · intro pid p found
    obtain ⟨old,resident,items⟩ := queues pid p found
    exact items ▸ inventory.queueUnique pid old resident
  · intro pid p other q found otherFound different id member otherMember
    obtain ⟨old,resident,items⟩ := queues pid p found
    obtain ⟨otherOld,otherResident,otherItems⟩ := queues other q otherFound
    exact inventory.peersSeparate pid old other otherOld resident otherResident different id
      (items ▸ member) (otherItems ▸ otherMember)
  · intro pid p found id member queued
    obtain ⟨old,resident,items⟩ := queues pid p found
    exact inventory.localsSeparate pid old resident id member (items ▸ queued)
  · intro id member
    obtain ⟨packet,resident⟩ := inventory.localResident id member
    exact packets id packet resident
  · intro pid p found id member
    obtain ⟨old,resident,items⟩ := queues pid p found
    obtain ⟨packet,cell⟩ := inventory.queueResident pid old resident id (items ▸ member)
    exact packets id packet cell

theorem TxInventory.points (inventory : TxInventory locals w)
    (same : ownershipPointView v = ownershipPointView w) : TxInventory locals v := by
  apply inventory.transport
  · intro pid p found
    have point := congrFun (congrArg (fun view => view.2.2.1) same) pid
    change (peerAt v pid).map peerOwnership = (peerAt w pid).map peerOwnership at point
    rw [found] at point
    obtain ⟨old,resident,fields⟩ := Option.map_eq_some_iff.mp point.symm
    exact ⟨old,resident,congrArg (fun fields : PeerOwnership => fields.2.1.flatten) fields⟩
  · intro id packet found
    have point := congrFun (congrArg (fun view => view.2.2.2.1) same) id
    change (Queues.TxDisposition.txPackets v id).map (·.keypair) =
      (Queues.TxDisposition.txPackets w id).map (·.keypair) at point
    rw [found] at point
    obtain ⟨current,resident,_⟩ := Option.map_eq_some_iff.mp point
    exact ⟨current,resident⟩

theorem TxInventory.peek (inventory : TxInventory locals w) (pid : PeerId)
    (a b : Ambient)
    (run : ((txPeekSource pid).run w).run a = .ok ((first,v),b)) : TxInventory locals v := by
  obtain ⟨d,p,queue,device,found,contents,_,after⟩ := txPeek_effect pid a b run
  rw [after]
  apply inventory.exchange device found
  simp only [txPeerItems,contents]
  exact List.Perm.refl _

end Leanux.Proofs.WG.RetirementSecurity
