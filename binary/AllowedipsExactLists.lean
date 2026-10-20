import AllowedipsOwnershipDisjoint

namespace Binary.Pair.Allowedips
open Leanux Leanux.WG

theorem Reconstructed.peer_at {names o m d id base count entries}
    (related : Corresponds names o m d) (named : (id,base) ∈ names.trie.peers)
    (member : (id,count,entries) ∈ (target d).peers) :
    (do
      let first ← word m "peer.list.head" (base+1096) 8
      peerList names m (base+1096) (names.trie.nodes.length+1) first (base+1096) [])=.ok entries := by
  obtain ⟨address,present,_,read⟩ := (reconstruct_fields related).peer member
  have equal := Index.unique_first (Trie.reconstruct_fields related.trie).peerIds present named
  simpa only [equal] using read

theorem Ring.owner_unlink_decodes {names o m head fuel entries removed previous next id value}
    (g : Geometry names o) (layout : o.nodeSize=72)
    (headSlot : LinkSlot names head) (previousSlot : LinkSlot names previous) (nextSlot : LinkSlot names next)
    (unique : (names.trie.nodes.map Prod.fst).Nodup)
    (focus : Ring.Fields names m head previous removed next id)
    (predecessor : word m "unlink.predecessor" previous 8=.ok removed)
    (successor : word m "peer.list.prev" (next+8) 8=.ok removed)
    (decoded : (do
      let first ← word m "peer.list.head" head 8
      peerList names m head fuel first head [])=.ok entries) :
    (do
      let memory := unlinkMemory (write64 m (removed-56) value) previous next
      let first ← word memory "peer.list.head" head 8
      peerList names memory head fuel first head [])=.ok (entries.filter (· != id)) := by
  have named : (id,removed-56) ∈ names.trie.nodes := focus.named
  have ownerFocus := focus.owner_frame g layout named (value:=value)
  have ownerDecoded := owner_decodes g layout headSlot named decoded (value:=value)
  have pred : word (write64 m (removed-56) value) "unlink.predecessor" previous 8=.ok removed := by
    have same := owner_word_frame (m:=m) (value:=value) g layout previousSlot named 0 (.inl rfl) "unlink.predecessor"
    simpa only [Nat.add_zero,predecessor] using same
  have succ : word (write64 m (removed-56) value) "peer.list.prev" (next+8) 8=.ok removed := by
    rw [owner_word_frame g layout nextSlot named 8 (.inr rfl)]
    exact successor
  exact unlink_decodes g layout headSlot previousSlot nextSlot unique ownerFocus pred succ ownerDecoded

namespace Exact

/-- All ordered ownership lists after the tested physical segment, derived
from full entry reconstruction and the same executable heap assertion. -/
theorem effect_lists {names o s memory regs d id base node pid peer owner}
    (related : Corresponds names o s.dmem d) (heap : heap names (target d) s.dmem=.ok ())
    (named : (id,base) ∈ names.trie.nodes) (present : d.nodes.get? id=some node)
    (peerNamed : (pid,peer) ∈ names.trie.peers) (hasPeer : d.peers.get? pid=some owner)
    (nodeAt : s.regs.rbx.toNat=base) (peerAt : s.regs.r14.toNat=peer)
    (checked : effect s=.ok (memory,regs)) :
    ∀ current address count entries, (current,address) ∈ names.trie.peers →
      (current,count,entries) ∈ (target d).peers →
      (do
        let first ← word memory "peer.list.head" (address+1096) 8
        peerList names memory (address+1096) (names.trie.nodes.length+1) first (address+1096) [])=
        .ok (if current=pid then entries.filter (· != id)++[id] else entries.filter (· != id)) := by
  have core := Trie.reconstruct_fields related.trie
  have g := geometry related
  have layout : o.nodeSize=72 := core.layout.1
  obtain ⟨previous,next,focus,previousSlot,nextSlot,predecessor,successor⟩ := focus_of_heap related heap named present peerNamed
  have back : word s.dmem "peer.list.prev" (s.regs.rbx.toNat+64) 8=.ok previous := by
    simpa only [nodeAt,Nat.add_assoc] using focus.back
  have forward : word s.dmem "peer.list.next" (s.regs.rbx.toNat+56) 8=.ok next := by simpa only [nodeAt] using focus.forward
  obtain ⟨last,tailRead,memoryEq⟩ := effect_ring g layout (.peer peerNamed) (by simpa only [nodeAt] using focus.slot)
    (by rw [peerAt]) back forward checked
  simp only [nodeAt,peerAt] at tailRead memoryEq
  let removed := Ring.unlinkMemory (write64 s.dmem base peer) previous next
  have removal (current address count entries) (currentNamed : (current,address) ∈ names.trie.peers)
      (member : (current,count,entries) ∈ (target d).peers) :
      (do
        let first ← word removed "peer.list.head" (address+1096) 8
        peerList names removed (address+1096) (names.trie.nodes.length+1) first (address+1096) [])=
        .ok (entries.filter (· != id)) := by
    have currentFocus := focus.rehead (node_peer_link_ne g layout named currentNamed)
    simpa only [Nat.add_sub_cancel] using Ring.owner_unlink_decodes g layout (.peer currentNamed)
      previousSlot nextSlot core.nodeIds currentFocus predecessor successor
      (Reconstructed.peer_at related currentNamed member) (value:=peer)
  have ownerMember : (pid,owner.refcount,owner.allowedipsList) ∈ (target d).peers := by
    exact List.mem_map.mpr ⟨(pid,owner),Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hasPeer,rfl⟩
  have targetDecoded := removal pid peer owner.refcount owner.allowedipsList peerNamed ownerMember
  have lastSlot := Ring.decoded_tail_slot (.peer peerNamed) targetDecoded tailRead
  intro current address count entries currentNamed member
  have currentFocus := focus.rehead (node_peer_link_ne g layout named currentNamed)
  have finalFocus := (currentFocus.owner_frame g layout named (value:=peer)).unlink_focus g layout previousSlot nextSlot
  have afterRemoval := removal current address count entries currentNamed member
  rw [memoryEq]
  by_cases same : current=pid
  · subst current
    have addressEq := Index.unique_first core.peerIds currentNamed peerNamed
    subst address
    simp only [ite_true]
    exact Ring.append_decodes g layout (.peer peerNamed) lastSlot finalFocus tailRead afterRemoval
      (by simp) core.nodeIds (Ring.append_budget finalFocus core.nodeIds afterRemoval (by simp))
  · simp only [same,ite_false]
    apply Ring.append_other g layout (.peer peerNamed) peerNamed rfl (.peer currentNamed) finalFocus
      (peer_heads_ne related currentNamed peerNamed same)
      (fun nodeId addr nodeNamed => node_peer_link_ne g layout nodeNamed currentNamed)
      tailRead targetDecoded afterRemoval
    · intro nodeId first second
      exact peer_lists_disjoint related heap ownerMember member (Ne.symm same) nodeId
        (List.mem_filter.mp first).1 (List.mem_filter.mp second).1
    · simp

#print axioms effect_lists
end Exact
end Binary.Pair.Allowedips
