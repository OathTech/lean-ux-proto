import AllowedipsRingBudget

namespace Binary.Pair.Allowedips.Ring

theorem Fields.owner_frame {names o m head previous link next id focusId base value}
    (fields : Fields names m head previous link next id)
    (g : Geometry names o) (layout : o.nodeSize=72) (named : (focusId,base) ∈ names.trie.nodes) :
    Fields names (write64 m base value) head previous link next id := by
  refine ⟨fields.known,fields.notHead,fields.valid,fields.owner,?_,?_⟩
  · rw [owner_word_frame g layout fields.slot named 8 (.inr rfl)]
    exact fields.back
  · have same := owner_word_frame (m:=m) (value:=value) g layout fields.slot named 0 (.inl rfl) "peer.list.next"
    simpa only [Nat.add_zero,fields.forward] using same

theorem owner_decodes {names o m head fuel entries id base value}
    (g : Geometry names o) (layout : o.nodeSize=72) (headSlot : LinkSlot names head)
    (named : (id,base) ∈ names.trie.nodes)
    (decoded : (do
      let first ← word m "peer.list.head" head 8
      peerList names m head fuel first head [])=.ok entries) :
    (do
      let first ← word (write64 m base value) "peer.list.head" head 8
      peerList names (write64 m base value) head fuel first head [])=.ok entries := by
  have same := peerList_congr names m (write64 m base value) head
    (fun path offset which => (owner_word_frame g layout headSlot named offset which path).symm)
    (fun _ _ member path offset which =>
      (owner_word_frame g layout (.node member) named offset which path).symm) fuel
  have firstSame := owner_word_frame (m:=m) (value:=value) g layout headSlot named 0 (.inl rfl) "peer.list.head"
  simp only [Nat.add_zero] at firstSame
  simp only [firstSame,←same]
  exact decoded

theorem Fields.unlink_focus {names o m head previous link next id}
    (fields : Fields names m head previous link next id)
    (g : Geometry names o) (layout : o.nodeSize=72)
    (previousSlot : LinkSlot names previous) (nextSlot : LinkSlot names next) :
    Fields names (unlinkMemory m previous next) head previous link next id := by
  refine ⟨fields.known,fields.notHead,fields.valid,fields.owner,?_,?_⟩
  · rw [unlink_back g layout previousSlot nextSlot fields.slot]
    simp only [fields.back,ite_self]
  · rw [unlink_forward g layout previousSlot nextSlot fields.slot]
    simp only [fields.forward,ite_self]

/-- The destination's decoder after the actual owner/unlink/append stores.
The tail read is an intermediate read, not the destination's old tail. The
source list effect is deletion followed by append, including same-list moves. -/
theorem reassign_decodes {names o m head entries removed oldPrev oldNext id newPeer last}
    (g : Geometry names o) (layout : o.nodeSize=72)
    (headSlot : LinkSlot names head) (previousSlot : LinkSlot names oldPrev)
    (nextSlot : LinkSlot names oldNext) (lastSlot : LinkSlot names last)
    (unique : (names.trie.nodes.map Prod.fst).Nodup)
    (focus : Fields names m head oldPrev removed oldNext id)
    (predecessor : word m "unlink.predecessor" oldPrev 8=.ok removed)
    (successor : word m "peer.list.prev" (oldNext+8) 8=.ok removed)
    (decoded : (do
      let first ← word m "peer.list.head" head 8
      peerList names m head (names.trie.nodes.length+1) first head [])=.ok entries)
    (tailRead : word (unlinkMemory (write64 m (removed-56) newPeer) oldPrev oldNext)
      "peer.list.prev" (head+8) 8=.ok last) :
    (do
      let memory := appendMemory (unlinkMemory (write64 m (removed-56) newPeer) oldPrev oldNext) head last removed
      let first ← word memory "peer.list.head" head 8
      peerList names memory head (names.trie.nodes.length+1) first head [])=
      .ok (entries.filter (· != id)++[id]) := by
  have named : (id,removed-56) ∈ names.trie.nodes := focus.named
  have ownerFocus := focus.owner_frame g layout named (value:=newPeer)
  have ownerDecoded := owner_decodes g layout headSlot named decoded (value:=newPeer)
  have pred : word (write64 m (removed-56) newPeer) "unlink.predecessor" oldPrev 8=.ok removed := by
    have same := owner_word_frame (m:=m) (value:=newPeer) g layout previousSlot named 0 (.inl rfl) "unlink.predecessor"
    simpa only [Nat.add_zero,predecessor] using same
  have succ : word (write64 m (removed-56) newPeer) "peer.list.prev" (oldNext+8) 8=.ok removed := by
    rw [owner_word_frame g layout nextSlot named 8 (.inr rfl)]
    exact successor
  have removedDecoded := unlink_decodes g layout headSlot previousSlot nextSlot unique ownerFocus pred succ ownerDecoded
  have removedFocus := ownerFocus.unlink_focus g layout previousSlot nextSlot
  have fresh : id ∉ entries.filter (· != id) := by simp
  exact append_decodes g layout headSlot lastSlot removedFocus tailRead removedDecoded fresh unique
    (append_budget removedFocus unique removedDecoded fresh)

#print axioms reassign_decodes
end Binary.Pair.Allowedips.Ring
