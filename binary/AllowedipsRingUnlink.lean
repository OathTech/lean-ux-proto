import AllowedipsRingMemory

namespace Binary.Pair.Allowedips.Ring
open Index (skip)

theorem Chain.unlink_fields {names o m head nodes link p q id removed oldPrev oldNext focusId}
    (g : Geometry names o) (layout : o.nodeSize=72)
    (previousSlot : LinkSlot names oldPrev) (nextSlot : LinkSlot names oldNext)
    (shape : Chain names m head head nodes) (member : (link,id) ∈ nodes)
    (fields : Fields names m head p link q id) (focus : Fields names m head oldPrev removed oldNext focusId)
    (predecessor : word m "unlink.predecessor" oldPrev 8=.ok removed)
    (successor : word m "peer.list.prev" (oldNext+8) 8=.ok removed) :
    Fields names (unlinkMemory m oldPrev oldNext) head (skip removed oldPrev p) link (skip removed oldNext q) id := by
  have neighbors := shape.neighbors member fields focus predecessor successor
  refine ⟨fields.known,fields.notHead,fields.valid,fields.owner,?_,?_⟩
  · rw [unlink_back g layout previousSlot nextSlot fields.slot]
    simp only [←neighbors.2,fields.back,skip]
    split <;> rfl
  · rw [unlink_forward g layout previousSlot nextSlot fields.slot]
    simp only [←neighbors.1,fields.forward,skip]
    split <;> rfl

theorem Chain.unlink_sentinel {names o m head nodes removed oldPrev oldNext id}
    (g : Geometry names o) (layout : o.nodeSize=72)
    (headSlot : LinkSlot names head) (previousSlot : LinkSlot names oldPrev) (nextSlot : LinkSlot names oldNext)
    (shape : Chain names m head head nodes) (focus : Fields names m head oldPrev removed oldNext id)
    (enter : word m "peer.list.head" head 8=.ok (first head nodes))
    (successor : word m "peer.list.prev" (oldNext+8) 8=.ok removed)
    (last : Nat) (back : word m "peer.list.prev" (head+8) 8=.ok last) :
    word (unlinkMemory m oldPrev oldNext) "peer.list.prev" (head+8) 8=.ok (skip removed oldPrev last) := by
  have lastNext := shape.last_forward (Binary.Pair.word_path enter "peer.list.next") back
  have same : head=oldNext ↔ last=removed := by
    constructor
    · intro equal
      exact word_values (equal ▸ back) successor
    · intro equal
      exact word_values (equal ▸ lastNext) focus.forward
  rw [unlink_back g layout previousSlot nextSlot headSlot]
  simp only [same,back,skip]
  split <;> rfl

theorem Chain.unlink_head {names o m head nodes removed oldPrev oldNext id}
    (g : Geometry names o) (layout : o.nodeSize=72)
    (headSlot : LinkSlot names head) (previousSlot : LinkSlot names oldPrev) (nextSlot : LinkSlot names oldNext)
    (shape : Chain names m head head nodes) (focus : Fields names m head oldPrev removed oldNext id)
    (enter : word m "peer.list.head" head 8=.ok (first head nodes))
    (predecessor : word m "unlink.predecessor" oldPrev 8=.ok removed) :
    word (unlinkMemory m oldPrev oldNext) "peer.list.head" head 8=.ok (skip removed oldNext (first head nodes)) := by
  have same : head=oldPrev ↔ first head nodes=removed := by
    constructor
    · intro equal
      have pred := predecessor
      rw [←equal] at pred
      exact word_values enter pred
    · exact shape.head_back focus
  rw [unlink_forward g layout previousSlot nextSlot headSlot]
  simp only [same,enter,skip]
  split <;> rfl

/-- Actual list_del stores reconstruct source identity deletion in every peer
ring. A focus absent from this ring leaves its decoded sequence unchanged. -/
theorem unlink_decodes {names o m head fuel entries removed oldPrev oldNext id}
    (g : Geometry names o) (layout : o.nodeSize=72)
    (headSlot : LinkSlot names head) (previousSlot : LinkSlot names oldPrev) (nextSlot : LinkSlot names oldNext)
    (unique : (names.trie.nodes.map Prod.fst).Nodup)
    (focus : Fields names m head oldPrev removed oldNext id)
    (predecessor : word m "unlink.predecessor" oldPrev 8=.ok removed)
    (successor : word m "peer.list.prev" (oldNext+8) 8=.ok removed)
    (decoded : (do
      let first ← word m "peer.list.head" head 8
      peerList names m head fuel first head [])=.ok entries) :
    (do
      let first ← word (unlinkMemory m oldPrev oldNext) "peer.list.head" head 8
      peerList names (unlinkMemory m oldPrev oldNext) head fuel first head [])=.ok (entries.filter (· != id)) := by
  obtain ⟨firstWord,headRead,run⟩ := bind_ok decoded
  obtain ⟨nodes,entriesEq,headEq,shape,_,_,_⟩ := peerList_shape run
  have enter : word m "peer.list.head" head 8=.ok (first head nodes) := by simpa only [headEq] using headRead
  obtain ⟨nodes',entriesEq',headEq',shape',after⟩ := peerList_erase run focus
    (shape.unlink_sentinel g layout headSlot previousSlot nextSlot focus enter successor)
    (by
      intro ns _ _ shape' link current p q member _ fields
      exact shape'.unlink_fields g layout previousSlot nextSlot member fields focus predecessor successor)
  have updatedHead := shape.unlink_head g layout headSlot previousSlot nextSlot focus enter predecessor
  rw [updatedHead]
  change peerList names (unlinkMemory m oldPrev oldNext) head fuel
    (skip removed oldNext (first head nodes)) head []=_
  have notRemoved : skip removed oldPrev head=head := ite_eq_right (Ne.symm focus.notHead)
  rw [notRemoved] at after
  rw [←headEq,after,shape'.erase_ids focus unique,←entriesEq']

#print axioms unlink_decodes
end Binary.Pair.Allowedips.Ring
