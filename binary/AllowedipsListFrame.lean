import AllowedipsExactLists

namespace Binary.Pair.Allowedips

/-- A frame footprint, not an additional reconstruction clause. -/
def ListWrites (names : Names) (a : BitVec 64) : Prop :=
  ∃ link, LinkSlot names link ∧ ∃ offset, (offset=0 ∨ offset=8) ∧ InRange (.ofNat 64 (link+offset)) 8 a

theorem list_write_frame {names m link offset value} (slot : LinkSlot names link)
    (which : offset=0 ∨ offset=8) : EqualOutside (ListWrites names) m (write64 m (link+offset) value) := by
  intro a outside
  exact write64_frame _ _ _ a (fun inside => outside ⟨link,slot,offset,which,inside⟩)

theorem list_frame_trans {names before middle after}
    (first : EqualOutside (ListWrites names) before middle)
    (second : EqualOutside (ListWrites names) middle after) : EqualOutside (ListWrites names) before after :=
  fun a outside => (first a outside).trans (second a outside)

theorem Ring.unlink_frame {names m previous next}
    (previousSlot : LinkSlot names previous) (nextSlot : LinkSlot names next) :
    EqualOutside (ListWrites names) m (unlinkMemory m previous next) := by
  unfold unlinkMemory
  apply list_frame_trans (list_write_frame nextSlot (.inr rfl))
  simpa only [Nat.add_zero] using list_write_frame (m:=write64 m (next+8) previous) (value:=next) previousSlot (.inl rfl)

theorem Ring.append_bytes_frame {names m head last added}
    (headSlot : LinkSlot names head) (lastSlot : LinkSlot names last) (addedSlot : LinkSlot names added) :
    EqualOutside (ListWrites names) m (appendMemory m head last added) := by
  unfold appendMemory
  apply list_frame_trans (list_write_frame headSlot (.inr rfl))
  have first : EqualOutside (ListWrites names) (write64 m (head+8) added)
      (write64 (write64 m (head+8) added) added head) := by
    simpa only [Nat.add_zero] using list_write_frame (m:=write64 m (head+8) added) (value:=head) addedSlot (.inl rfl)
  apply list_frame_trans first
  apply list_frame_trans (list_write_frame addedSlot (.inr rfl))
  simpa only [Nat.add_zero] using list_write_frame
    (m:=write64 (write64 (write64 m (head+8) added) added head) (added+8) last) (value:=added) lastSlot (.inl rfl)

theorem node_before_list_apart {names o id base offset size}
    (g : Geometry names o) (layout : o.nodeSize=72) (named : (id,base) ∈ names.trie.nodes)
    (within : offset+size≤56) :
    ∀ a, InRange (.ofNat 64 (base+offset)) size a → ¬ListWrites names a := by
  rintro a inside ⟨link,slot,field,which,write⟩
  cases slot with
  | node other =>
    exact g.slices_apart (node_allocation named) (node_allocation other) offset size (56+field) 8
      (by dsimp only; rw [layout]; omega) (by dsimp only; rw [layout]; rcases which with rfl|rfl <;> decide)
      (fun _ => .inl (by omega)) a inside (by simpa only [Nat.add_assoc] using write)
  | peer other =>
    exact g.slices_apart (node_allocation named) (peer_allocation other) offset size (1096+field) 8
      (by dsimp only; rw [layout]; omega) (by dsimp only; rcases which with rfl|rfl <;> decide)
      (fun _ => .inl (by omega)) a inside (by simpa only [Nat.add_assoc] using write)

theorem peer_count_list_apart {names o id base}
    (g : Geometry names o) (layout : o.nodeSize=72) (named : (id,base) ∈ names.trie.peers) :
    ∀ a, InRange (.ofNat 64 (base+Layouts.peer_refcount)) 4 a → ¬ListWrites names a := by
  rintro a inside ⟨link,slot,field,which,write⟩
  cases slot with
  | node other =>
    exact g.slices_apart (peer_allocation named) (node_allocation other) Layouts.peer_refcount 4 (56+field) 8
      (by dsimp only; decide) (by dsimp only; rw [layout]; rcases which with rfl|rfl <;> decide)
      (fun equal => by have sizes := congrArg Prod.snd equal; change Layouts.peerSize=o.nodeSize at sizes;
                       rw [layout] at sizes; contradiction)
      a inside (by simpa only [Nat.add_assoc] using write)
  | peer other =>
    exact g.slices_apart (peer_allocation named) (peer_allocation other) Layouts.peer_refcount 4 (1096+field) 8
      (by dsimp only; decide) (by dsimp only; rcases which with rfl|rfl <;> decide)
      (fun _ => .inl (by change 1056+4≤1096+field; omega))
      a inside (by simpa only [Nat.add_assoc] using write)

/-- Derive the write frame of all six list-link stores from the full entry
assertion. Owner replacement is left separate for record reconstruction. -/
theorem Exact.effect_list_frame {names o s memory regs d id base node pid peer owner}
    (related : Corresponds names o s.dmem d) (heap : heap names (target d) s.dmem=.ok ())
    (named : (id,base) ∈ names.trie.nodes) (present : d.nodes.get? id=some node)
    (peerNamed : (pid,peer) ∈ names.trie.peers) (hasPeer : d.peers.get? pid=some owner)
    (nodeAt : s.regs.rbx.toNat=base) (peerAt : s.regs.r14.toNat=peer)
    (checked : Exact.effect s=.ok (memory,regs)) :
    EqualOutside (ListWrites names) (write64 s.dmem base peer) memory := by
  have core := Trie.reconstruct_fields related.trie
  have g := geometry related
  have layout : o.nodeSize=72 := core.layout.1
  obtain ⟨previous,next,focus,previousSlot,nextSlot,predecessor,successor⟩ := focus_of_heap related heap named present peerNamed
  have back : word s.dmem "peer.list.prev" (s.regs.rbx.toNat+64) 8=.ok previous := by
    simpa only [nodeAt,Nat.add_assoc] using focus.back
  have forward : word s.dmem "peer.list.next" (s.regs.rbx.toNat+56) 8=.ok next := by simpa only [nodeAt] using focus.forward
  obtain ⟨last,tailRead,memoryEq⟩ := Exact.effect_ring g layout (.peer peerNamed) (by simpa only [nodeAt] using focus.slot)
    (by rw [peerAt]) back forward checked
  simp only [nodeAt,peerAt] at tailRead memoryEq
  have ownerMember : (pid,owner.refcount,owner.allowedipsList) ∈ (target d).peers := by
    exact List.mem_map.mpr ⟨(pid,owner),Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hasPeer,rfl⟩
  have removed := Ring.owner_unlink_decodes g layout (.peer peerNamed) previousSlot nextSlot core.nodeIds focus
    predecessor successor (Reconstructed.peer_at related peerNamed ownerMember) (value:=peer)
  simp only [Nat.add_sub_cancel] at removed
  have lastSlot := Ring.decoded_tail_slot (.peer peerNamed) removed tailRead
  rw [memoryEq]
  exact list_frame_trans (Ring.unlink_frame previousSlot nextSlot) (Ring.append_bytes_frame (.peer peerNamed) lastSlot focus.slot)

#print axioms Exact.effect_list_frame
end Binary.Pair.Allowedips
