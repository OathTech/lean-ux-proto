import AllowedipsOwnersUpdate

namespace Binary.Pair.Allowedips
open Leanux Leanux.WG

theorem readNat_of_word {m path address size value}
    (decoded : word m path address size=.ok value) :
    readNat ⟨{dmem := m},0⟩ address size=.ok value := by
  have loaded := word_loadInt _ _ _ _ _ decoded
  unfold word at decoded
  split at decoded
  · cases bytes : m.loadBytes (.ofNat 64 address) size with
    | none => rw [bytes] at decoded; cases decoded
    | some data =>
      have read : readNat ⟨{dmem := m},0⟩ address size=
          .ok ((data.zipIdx.map fun (b,i) => b.toNat*256^i).sum) := by
        simp only [readNat,bytes]
        rfl
      have equal := Int.ofNat.inj (Option.some.inj ((Trie.readNat_loadInt read).symm.trans loaded))
      exact equal ▸ read
  · cases decoded

theorem internalListCheck_of_words {names m id base}
    (unique : (names.trie.nodes.map Prod.fst).Nodup) (named : (id,base) ∈ names.trie.nodes)
    (forward : word m "peer.list.next" (base+56) 8=.ok (base+56))
    (back : word m "peer.list.prev" (base+64) 8=.ok (base+56)) : internalListCheck names m id=.ok () := by
  have address : Trie.address names.trie.nodes (some id)=.ok base := by
    simp only [Trie.address,Trie.find_identity unique named]
    rfl
  have f := readNat_of_word forward
  have b := readNat_of_word back
  simp only [internalListCheck,address,AllowedipsMutationLayout.peer_list,Nat.add_assoc]
  change (do
    let next ← readNat ⟨{dmem:=m},0⟩ (base+56) 8
    let prev ← readNat ⟨{dmem:=m},0⟩ (base+64) 8
    unless next==base+56 && prev==base+56 do throw "heap.internal-list")=.ok ()
  rw [f]
  change (do
    let prev ← readNat ⟨{dmem:=m},0⟩ (base+64) 8
    unless base+56==base+56 && prev==base+56 do throw "heap.internal-list")=.ok ()
  rw [b]
  dsimp only [Bind.bind,Except.bind]
  simp only [beq_self_eq_true,Bool.and_self,ite_true]
  rfl

namespace Ring

/-- A different self-linked internal node cannot be a changed neighbor or
the destination tail. Those exclusions follow from the actual ring words. -/
theorem reassign_internal {names o m head previous focus next id other current value fuel entries last}
    (g : Geometry names o) (layout : o.nodeSize=72) (headSlot : LinkSlot names head)
    (previousSlot : LinkSlot names previous) (nextSlot : LinkSlot names next)
    (removed : Fields names m head previous focus next id)
    (internal : Fields names m head other other other current)
    (different : other≠focus)
    (pred : word m "unlink.predecessor" previous 8=.ok focus)
    (succ : word m "peer.list.prev" (next+8) 8=.ok focus)
    (decoded : (do
      let first ← word (unlinkMemory (write64 m (focus-56) value) previous next) "peer.list.head" head 8
      peerList names (unlinkMemory (write64 m (focus-56) value) previous next) head fuel first head [])=.ok entries)
    (tail : word (unlinkMemory (write64 m (focus-56) value) previous next) "peer.list.prev" (head+8) 8=.ok last) :
    let after := appendMemory (unlinkMemory (write64 m (focus-56) value) previous next) head last focus
    word after "peer.list.next" other 8=.ok other ∧ word after "peer.list.prev" (other+8) 8=.ok other := by
  have notPrevious : other≠previous := by
    intro same
    have read := pred
    rw [←same] at read
    exact different (word_values internal.forward read)
  have notNext : other≠next := by
    intro same
    have read := succ
    rw [←same] at read
    exact different (word_values internal.back read)
  have afterForward : word (unlinkMemory (write64 m (focus-56) value) previous next) "peer.list.next" other 8=.ok other := by
    rw [unlink_forward g layout previousSlot nextSlot internal.slot,ite_eq_right notPrevious]
    have framed := owner_word_frame (m:=m) (value:=value) g layout internal.slot removed.named 0 (.inl rfl) "peer.list.next"
    simpa only [Nat.add_zero,internal.forward,AllowedipsMutationLayout.peer_list] using framed
  have afterBack : word (unlinkMemory (write64 m (focus-56) value) previous next) "peer.list.prev" (other+8) 8=.ok other := by
    rw [unlink_back g layout previousSlot nextSlot internal.slot,ite_eq_right notNext]
    have framed := owner_word_frame (m:=m) (value:=value) g layout internal.slot removed.named 8 (.inr rfl) "peer.list.prev"
    simpa only [internal.back,AllowedipsMutationLayout.peer_list] using framed
  have lastSlot := decoded_tail_slot headSlot decoded tail
  obtain ⟨firstWord,firstRead,run⟩ := bind_ok decoded
  obtain ⟨nodes,_,headEq,shape,_,_,_⟩ := peerList_shape run
  have enter : word (unlinkMemory (write64 m (focus-56) value) previous next) "peer.list.next" head 8=
      .ok (first head nodes) := by
    exact Binary.Pair.word_path (headEq ▸ firstRead) _
  have lastForward := shape.last_forward enter tail
  have notLast : other≠last := by
    intro same
    have read := lastForward
    rw [←same] at read
    exact internal.notHead (word_values afterForward read)
  dsimp only
  constructor
  · rw [append_forward g layout headSlot lastSlot removed.slot internal.slot,
      ite_eq_right notLast,ite_eq_right different]
    exact afterForward
  · rw [append_back g layout headSlot lastSlot removed.slot internal.slot,
      ite_eq_right different,ite_eq_right internal.notHead]
    exact afterBack

end Ring
#print axioms Ring.reassign_internal
end Binary.Pair.Allowedips
