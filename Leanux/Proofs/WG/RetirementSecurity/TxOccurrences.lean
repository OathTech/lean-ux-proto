import Leanux.Proofs.WG.RetirementSecurity.TxWorkerHolders
import Leanux.Proofs.WG.RetirementSecurity.TxAllocationHolders

/-! Physical TX occurrences at native caller cuts. Peer queues own batches;
their device-ring entries are aliases. The explicit held list contains
newly allocated unpublished batches or batches removed for TX disposal.
Uniqueness covers every packet in every batch, not only reference-bearing
heads. The projection concerns one resident device epoch at a time. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes
variable {id : SkbId}

inductive TxLocalPhase where
  | unpublished
  | selected
  deriving DecidableEq

structure TxLocalBatch where
  phase : TxLocalPhase
  peer : PeerId
  items : List SkbId
  deriving DecidableEq

def txLocalItems (locals : List TxLocalBatch) : List SkbId := locals.flatMap (·.items)
def txPeerItems (p : Peer) : List SkbId := p.txQueue.all.flatten

structure TxInventory (locals : List TxLocalBatch) (w : WGWorld) : Prop where
  localUnique : (txLocalItems locals).Nodup
  queueUnique : ∀ pid p, peerAt w pid = some p → (txPeerItems p).Nodup
  peersSeparate : ∀ pid p other q, peerAt w pid = some p → peerAt w other = some q →
    pid ≠ other → ∀ id, id ∈ txPeerItems p → id ∉ txPeerItems q
  localsSeparate : ∀ pid p, peerAt w pid = some p →
    ∀ id, id ∈ txLocalItems locals → id ∉ txPeerItems p
  localResident : ∀ id, id ∈ txLocalItems locals →
    ∃ packet, Queues.TxDisposition.txPackets w id = some packet
  queueResident : ∀ pid p, peerAt w pid = some p → ∀ id, id ∈ txPeerItems p →
    ∃ packet, Queues.TxDisposition.txPackets w id = some packet

theorem TxInventory.combined_unique (inventory : TxInventory locals w)
    (found : peerAt w pid = some p) : (txLocalItems locals ++ txPeerItems p).Nodup := by
  refine List.nodup_append.mpr ⟨inventory.localUnique,inventory.queueUnique pid p found,?_⟩
  intro id member other queued same
  subst other
  exact inventory.localsSeparate pid p found id member queued

theorem TxInventory.combined_resident (inventory : TxInventory locals w)
    (found : peerAt w pid = some p) (member : id ∈ txLocalItems locals ++ txPeerItems p) :
    ∃ packet, Queues.TxDisposition.txPackets w id = some packet := by
  rcases List.mem_append.mp member with held | queued
  · exact inventory.localResident id held
  · exact inventory.queueResident pid p found id queued

theorem TxInventory.combined_separate (inventory : TxInventory locals w)
    (found : peerAt w pid = some p) (otherFound : peerAt w other = some q)
    (different : pid ≠ other) (member : id ∈ txLocalItems locals ++ txPeerItems p) :
    id ∉ txPeerItems q := by
  rcases List.mem_append.mp member with held | queued
  · exact inventory.localsSeparate other q otherFound id held
  · exact inventory.peersSeparate pid p other q found otherFound different id queued

theorem TxInventory.separated (inventory : TxInventory locals w) (pid : PeerId) : TxSeparated pid w := by
  intro p found items rest queue other q otherFound batch member head first inside
  have headMember : head ∈ batch := List.mem_of_mem_head? (by simp [first])
  by_cases same : pid = other
  · subst other
    have peerSame : q = p := Option.some.inj (otherFound.symm.trans found)
    subst q
    have unique := inventory.queueUnique pid p found
    have split : txPeerItems p = items ++ rest.flatten := by simp [txPeerItems,queue]
    rw [split] at unique
    have tailMember : head ∈ rest.flatten := List.mem_flatten.mpr ⟨batch,by simpa using member,headMember⟩
    exact (List.nodup_append.mp unique).2.2 head inside head tailMember rfl
  · have selected : head ∈ txPeerItems p := by simp [txPeerItems,queue,inside]
    have queued : head ∈ txPeerItems q := List.mem_flatten.mpr
      ⟨batch,by simpa [same] using member,headMember⟩
    exact inventory.peersSeparate pid p other q found otherFound same head selected queued

theorem TxInventory.local_detached (inventory : TxInventory (held :: locals) w) :
    TxDetached held.items w := by
  intro pid p found batch queued head first inside
  apply inventory.localsSeparate pid p found head (by simp [txLocalItems,inside])
  exact List.mem_flatten.mpr ⟨batch,queued,List.mem_of_mem_head? (by simp [first])⟩

end Leanux.Proofs.WG.RetirementSecurity
