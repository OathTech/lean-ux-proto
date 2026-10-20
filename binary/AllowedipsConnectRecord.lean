import AllowedipsRootPublishDecode

namespace Binary.Pair.Allowedips
open Leanux.WG

private theorem ok_bind (value : α) (f : α → Except ε β) :
    ((Except.ok value : Except ε α) >>= f)=f value := rfl

/-- The common two-word linkage effect. The packed parent can designate a
root slot or either child slot; its interpretation is proved by the caller. -/
def connectMemory (m : DataMem) (base slot packed : Nat) : DataMem :=
  write64 (write64 m (base+48) packed) slot base

theorem connect_record {names : Names} {m : DataMem} {id base slot packed : Nat}
    {node : Trie.Node} {parentSlot : Slot}
    (extent : base+56≤2^64) (slotExtent : slot+8≤2^64) (small : packed<2^64)
    (core : Trie.decodeNode names.trie Root.nodeOffsets m base=.ok node)
    (parentDecoded : parent names packed=.ok parentSlot)
    (apart : ∀ a, InRange (.ofNat 64 base) 56 a → ¬InRange (.ofNat 64 slot) 8 a) :
    decodeNode names Root.nodeOffsets (connectMemory m base slot packed) id base=
      .ok (id,({
        peer:=node.peer,bit:=node.children,cidr:=node.cidr,bitlen:=node.width,
        bits:=node.key,parent:=parentSlot} : AipNode)) ∧
    word (connectMemory m base slot packed) "node.link" slot 8=.ok base := by
  let middle := write64 m (base+48) packed
  have keep (offset size : Nat) (within : offset+size≤56) (path : String) :
      word (connectMemory m base slot packed) path (base+offset) size=
        word middle path (base+offset) size := by
    apply word_write64_frame
    intro a inside
    apply apart a
    obtain ⟨i,bound,equal⟩ := inside
    refine ⟨offset+i,by omega,?_⟩
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using equal
  have coreSame : Trie.decodeNode names.trie Root.nodeOffsets (connectMemory m base slot packed) base=
      Trie.decodeNode names.trie Root.nodeOffsets m base := by
    apply Trie.decodeNode_congr
    intro offset size field path
    have within : offset+size≤48 := by
      simp only [Trie.nodeSpans,Root.nodeOffsets,AllowedipsLayout.peer,AllowedipsLayout.bit,
        AllowedipsLayout.cidr,AllowedipsLayout.bit_at_a,AllowedipsLayout.bit_at_b,
        AllowedipsLayout.bitlen,AllowedipsLayout.bits,List.mem_cons,List.not_mem_nil,
        or_false,Prod.mk.injEq] at field
      omega
    rw [keep offset size (by omega) path]
    unfold middle write64
    rw [←Root.store_nat64]
    exact Root.word_store_frame m path base offset size 48 8 packed
      (by omega) (by decide) (.inl within)
  have parentRead : word (connectMemory m base slot packed) "node.parent" (base+48) 8=.ok packed := by
    rw [keep 48 8 (by decide) "node.parent"]
    exact word_write64_same m _ _ _ extent small
  constructor
  · simp only [decodeNode,coreSame,core,AllowedipsMutationLayout.parent_bit_packed,parentRead,parentDecoded,ok_bind]
    rfl
  · exact word_write64_same _ _ _ _ slotExtent (by omega)

#print axioms connect_record
end Binary.Pair.Allowedips
