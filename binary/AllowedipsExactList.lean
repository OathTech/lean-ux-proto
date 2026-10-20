import AllowedipsExactRing

namespace Binary.Pair.Allowedips.Exact
local instance : Labels := Image.linkedLabels

/-- The tested exact effect reconstructs the destination's actual source list
operation. The read of the post-unlink tail supplies its own named slot. -/
theorem effect_destination {names o s memory regs head previous next id entries}
    (g : Geometry names o) (layout : o.nodeSize=72)
    (headSlot : LinkSlot names head) (previousSlot : LinkSlot names previous) (nextSlot : LinkSlot names next)
    (headEq : head=s.regs.r14.toNat+1096)
    (unique : (names.trie.nodes.map Prod.fst).Nodup)
    (focus : Ring.Fields names s.dmem head previous (s.regs.rbx.toNat+56) next id)
    (predecessor : word s.dmem "unlink.predecessor" previous 8=.ok (s.regs.rbx.toNat+56))
    (successor : word s.dmem "peer.list.prev" (next+8) 8=.ok (s.regs.rbx.toNat+56))
    (decoded : (do
      let first ← word s.dmem "peer.list.head" head 8
      peerList names s.dmem head (names.trie.nodes.length+1) first head [])=.ok entries)
    (checked : effect s=.ok (memory,regs)) :
    (do
      let first ← word memory "peer.list.head" head 8
      peerList names memory head (names.trie.nodes.length+1) first head [])=
      .ok (entries.filter (· != id)++[id]) := by
  have back : word s.dmem "peer.list.prev" (s.regs.rbx.toNat+64) 8=.ok previous := by
    simpa only [Nat.add_assoc] using focus.back
  obtain ⟨last,tailRead,memoryEq⟩ := effect_ring g layout headSlot focus.slot headEq back focus.forward checked
  have named : (id,s.regs.rbx.toNat) ∈ names.trie.nodes := by
    simpa only [AllowedipsMutationLayout.peer_list,Nat.add_sub_cancel] using focus.named
  have ownerFocus := focus.owner_frame g layout named (value:=s.regs.r14.toNat)
  have ownerDecoded := Ring.owner_decodes g layout headSlot named decoded (value:=s.regs.r14.toNat)
  have pred : word (write64 s.dmem s.regs.rbx.toNat s.regs.r14.toNat) "unlink.predecessor" previous 8=
      .ok (s.regs.rbx.toNat+56) := by
    have same := Ring.owner_word_frame (m:=s.dmem) (value:=s.regs.r14.toNat) g layout previousSlot named 0 (.inl rfl) "unlink.predecessor"
    simpa only [Nat.add_zero,predecessor] using same
  have succ : word (write64 s.dmem s.regs.rbx.toNat s.regs.r14.toNat) "peer.list.prev" (next+8) 8=
      .ok (s.regs.rbx.toNat+56) := by
    rw [Ring.owner_word_frame g layout nextSlot named 8 (.inr rfl)]
    exact successor
  have removedDecoded := Ring.unlink_decodes g layout headSlot previousSlot nextSlot unique ownerFocus pred succ ownerDecoded
  have lastSlot := Ring.decoded_tail_slot headSlot removedDecoded tailRead
  have result := Ring.reassign_decodes g layout headSlot previousSlot nextSlot lastSlot unique focus
    predecessor successor decoded (newPeer:=s.regs.r14.toNat) (by simpa only [Nat.add_sub_cancel] using tailRead)
  simpa only [Nat.add_sub_cancel,←memoryEq] using result

/-- Concrete binary execution plus the destination-list portion of the
mutation correspondence. This is not the full insertion postcondition. -/
theorem segment_destination (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    {names o s memory regs head previous next id entries}
    (g : Geometry names o) (layout : o.nodeSize=72)
    (headSlot : LinkSlot names head) (previousSlot : LinkSlot names previous) (nextSlot : LinkSlot names next)
    (headEq : head=s.regs.r14.toNat+1096)
    (unique : (names.trie.nodes.map Prod.fst).Nodup)
    (focus : Ring.Fields names s.dmem head previous (s.regs.rbx.toNat+56) next id)
    (predecessor : word s.dmem "unlink.predecessor" previous 8=.ok (s.regs.rbx.toNat+56))
    (successor : word s.dmem "peer.list.prev" (next+8) 8=.ok (s.regs.rbx.toNat+56))
    (decoded : (do
      let first ← word s.dmem "peer.list.head" head 8
      peerList names s.dmem head (names.trie.nodes.length+1) first head [])=.ok entries)
    (checked : effect s=.ok (memory,regs)) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=AllowedipsMutationImage.Add.entry+0x549 ∧ t.data.regs=regs ∧
      (do
        let first ← word t.data.dmem "peer.list.head" head 8
        peerList names t.data.dmem head (names.trie.nodes.length+1) first head [])=
        .ok (entries.filter (· != id)++[id]))
      ⟨s,AllowedipsMutationImage.Add.entry+0x3e5⟩ := by
  have result := effect_destination g layout headSlot previousSlot nextSlot headEq unique focus
    predecessor successor decoded checked
  apply eventually_weaken (instructionStep fetch) _ _ _ _ (effect_segment fetch decoder checked)
  rintro t ⟨pc,mem,reg⟩
  exact ⟨pc,reg,by simpa only [mem] using result⟩

#print axioms segment_destination
end Binary.Pair.Allowedips.Exact
