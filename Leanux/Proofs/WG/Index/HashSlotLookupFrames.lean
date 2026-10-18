import Leanux.Proofs.WG.Index.HashSlotModel
import Leanux.Proofs.WG.Index.OwnerCoherenceFrames

/-! Physical coverage transport observes only the table, optional peer slots
and optional key owner words. Reference-count changes do not invent slots. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

theorem hashSlotCoverage_transport (before after : Device)
    (table : after.indexTable = before.indexTable)
    (peers : ∀ pid : PeerId, after.peers[pid]?.map clearKeys = before.peers[pid]?.map clearKeys)
    (keys : ∀ kid : KeypairId, after.keypairs[kid]?.map Keypair.peer = before.keypairs[kid]?.map Keypair.peer)
    (covered : HashSlotCoverage before) : HashSlotCoverage after := by
  intro entry member kid owner
  obtain ⟨pid,p,key,peerStored,keyStored,word,slot⟩ :=
    covered entry (table ▸ member) kid owner
  have peerMap : after.peers[pid]?.map clearKeys = some (clearKeys p) := by
    rw [peers pid,peerStored]
    rfl
  have keyMap : after.keypairs[kid]?.map Keypair.peer = some key.peer := by
    rw [keys kid,keyStored]
    rfl
  obtain ⟨q,peerAfter,slots⟩ := Option.map_eq_some_iff.mp peerMap
  obtain ⟨newKey,keyAfter,ownerAfter⟩ := Option.map_eq_some_iff.mp keyMap
  exact ⟨pid,q,newKey,peerAfter,keyAfter,ownerAfter.trans word,slots ▸ slot⟩

theorem hashSlotCoverage_peerWrite (d : Device) (pid : PeerId) (p next : Peer)
    (resident : d.peers[pid]? = some p) (slots : clearKeys next = clearKeys p)
    (covered : HashSlotCoverage d) :
    HashSlotCoverage {d with peers := d.peers.insert pid next} := by
  refine hashSlotCoverage_transport d {d with peers := d.peers.insert pid next} rfl ?_ (fun _ => rfl) covered
  intro target
  by_cases same : pid = target
  · subst target
    simp [resident,slots]
  · simp [Std.TreeMap.getElem?_insert,same]

theorem hashSlotCoverage_acquire (d : Device) (pid : PeerId) (p : Peer)
    (resident : d.peers[pid]? = some p) (covered : HashSlotCoverage d) :
    HashSlotCoverage (acquirePeer d pid p) :=
  hashSlotCoverage_peerWrite d pid p _ resident rfl covered

theorem hashSlotCoverage_write_same (d : Device) (writer : IndexOwner) (word : Option PeerId)
    (same : ownerWord d writer = some word) (covered : HashSlotCoverage d) :
    HashSlotCoverage (writeOwnerWord d writer word) := by
  apply hashSlotCoverage_transport d (writeOwnerWord d writer word) _ _ _ covered
  · cases writer <;> simp only [writeOwnerWord] <;> split <;> rfl
  · intro pid
    rw [writeOwnerWord_same_peers d writer word same]
  · intro kid
    rw [writeOwnerWord_same_keypairs d writer word same]

end Leanux.Proofs.WG.Index
