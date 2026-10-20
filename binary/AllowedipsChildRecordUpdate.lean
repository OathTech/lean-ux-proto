import AllowedipsDecodeChildren
import AllowedipsConnectRecord

namespace Binary.Pair.Allowedips
open Root

private theorem ok_bind (value : α) (f : α → Except ε β) :
    ((Except.ok value : Except ε α) >>= f)=f value := rfl

theorem core_child_write {names : Names} {m : DataMem} {base direction raw : Nat}
    {node : Trie.Node} {child : Option Nat}
    (bit : direction<2) (extent : base+56≤2^64) (small : raw<2^64)
    (read : Trie.decodeNode names.trie nodeOffsets m base=.ok node)
    (pointer : ∀ path, Trie.pointer names.trie.nodes path raw=.ok child) :
    Trie.decodeNode names.trie nodeOffsets (write64 m (base+8+direction*8) raw) base=
      .ok {node with children:=node.children.set! direction child} := by
  have fields := Trie.decodeNode_fields read
  obtain ⟨left,right,lp,rp,shape,leftRead,leftPointer,rightRead,rightPointer⟩ := fields.children
  have same (offset size : Nat) (field : (offset,size) ∈ Trie.nodeSpans nodeOffsets)
      (notLeft : offset≠nodeOffsets.children) (notRight : offset≠nodeOffsets.children+8) (path : String) :
      word (write64 m (base+8+direction*8) raw) path (base+offset) size=word m path (base+offset) size := by
    have apart : offset+size≤8 ∨ 24≤offset := by
      simp only [Trie.nodeSpans,nodeOffsets,AllowedipsLayout.peer,AllowedipsLayout.bit,
        AllowedipsLayout.cidr,AllowedipsLayout.bit_at_a,AllowedipsLayout.bit_at_b,
        AllowedipsLayout.bitlen,AllowedipsLayout.bits,List.mem_cons,List.not_mem_nil,
        or_false,Prod.mk.injEq] at field
      change offset≠8 at notLeft
      change offset≠8+8 at notRight
      omega
    have within : offset+size≤48 := by
      simp only [Trie.nodeSpans,nodeOffsets,AllowedipsLayout.peer,AllowedipsLayout.bit,
        AllowedipsLayout.cidr,AllowedipsLayout.bit_at_a,AllowedipsLayout.bit_at_b,
        AllowedipsLayout.bitlen,AllowedipsLayout.bits,List.mem_cons,List.not_mem_nil,
        or_false,Prod.mk.injEq] at field
      omega
    unfold write64
    rw [←store_nat64,Nat.add_assoc]
    exact word_store_frame m path base offset size (8+direction*8) 8 raw
      (by omega) (by omega) (by omega)
  have separate : ∀ offset ∈ [nodeOffsets.peer,nodeOffsets.cidr,nodeOffsets.bitlen,
      nodeOffsets.bitAtA,nodeOffsets.bitAtB,nodeOffsets.bits,nodeOffsets.bits+8],
      offset≠nodeOffsets.children ∧ offset≠nodeOffsets.children+8 := by
    decide
  have which : direction=0 ∨ direction=1 := by omega
  rcases which with rfl|rfl
  · have oldRight : word (write64 m (base+8+0*8) raw) "node.child[1]" (base+nodeOffsets.children+8) 8=.ok rp := by
      unfold write64
      rw [←store_nat64]
      change word (m.storeInt (.ofNat 64 (base+8)) 8 raw) "node.child[1]" (base+8+8) 8=.ok rp
      rw [Nat.add_assoc,word_store_frame m _ base 16 8 8 8 raw (by decide) (by decide) (.inr (by decide))]
      exact rightRead
    have changed := fields.change_children (left:=child) (right:=right)
      ⟨raw,rp,by simpa [nodeOffsets,AllowedipsLayout.bit] using
          word_write64_same m "node.child[0]" (base+8) raw (by omega) small,
        pointer _,oldRight,rightPointer⟩ same separate
    have children : node.children.set! 0 child=#[child,right] := by rw [shape]; rfl
    simpa only [children] using changed.decode
  · have oldLeft : word (write64 m (base+8+1*8) raw) "node.child[0]" (base+nodeOffsets.children) 8=.ok lp := by
      unfold write64
      rw [←store_nat64]
      change word (m.storeInt (.ofNat 64 (base+8+8)) 8 raw) "node.child[0]" (base+8) 8=.ok lp
      rw [Nat.add_assoc,word_store_frame m _ base 8 8 16 8 raw (by decide) (by decide) (.inl (by decide))]
      exact leftRead
    have newRight : word (write64 m (base+8+1*8) raw) "node.child[1]" (base+nodeOffsets.children+8) 8=.ok raw := by
      simpa [nodeOffsets,AllowedipsLayout.bit,Nat.add_assoc] using
        word_write64_same m "node.child[1]" (base+16) raw (by omega) small
    have changed := fields.change_children (left:=left) (right:=child)
      ⟨lp,raw,oldLeft,leftPointer,newRight,pointer _⟩ same separate
    have children : node.children.set! 1 child=#[left,child] := by rw [shape]; rfl
    simpa only [children] using changed.decode

#print axioms core_child_write

/-- Updating a child word also preserves the existing packed parent field.
This is the complete parent record, not just the core used by lookup. -/
theorem record_child_write {names : Names} {m : DataMem} {base direction raw id current : Nat}
    {node : Leanux.WG.AipNode} {child : Option Nat}
    (bit : direction<2) (extent : base+56≤2^64) (small : raw<2^64)
    (read : decodeNode names nodeOffsets m id base=.ok (current,node))
    (pointer : ∀ path, Trie.pointer names.trie.nodes path raw=.ok child) :
    decodeNode names nodeOffsets (write64 m (base+8+direction*8) raw) id base=
      .ok (current,{node with bit:=node.bit.set! direction child}) := by
  unfold decodeNode at read
  obtain ⟨core,coreRead,read⟩ := bind_ok read
  obtain ⟨parentWord,parentRead,read⟩ := bind_ok read
  obtain ⟨slot,slotRead,read⟩ := bind_ok read
  cases Except.ok.inj read
  have changed := core_child_write bit extent small coreRead pointer
  have parentSame : word (write64 m (base+8+direction*8) raw) "node.parent" (base+48) 8=.ok parentWord := by
    unfold write64
    rw [←store_nat64,Nat.add_assoc]
    rw [word_store_frame m _ base 48 8 (8+direction*8) 8 raw
      (by decide) (by omega) (.inr (by omega))]
    exact parentRead
  simp only [decodeNode,changed,AllowedipsMutationLayout.parent_bit_packed,parentSame,slotRead,
    ok_bind]
  rfl

#print axioms record_child_write
end Binary.Pair.Allowedips
