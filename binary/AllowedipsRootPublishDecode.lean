import AllowedipsRootRecord

namespace Binary.Pair.Allowedips.Root
open Leanux Leanux.WG

private theorem ok_bind (value : α) (f : α → Except ε β) :
    ((Except.ok value : Except ε α) >>= f)=f value := rfl

private theorem core_field_within {offset size : Nat}
    (field : (offset,size) ∈ Trie.nodeSpans nodeOffsets) : offset+size≤48 := by
  simp only [Trie.nodeSpans,nodeOffsets,AllowedipsLayout.peer,AllowedipsLayout.bit,
    AllowedipsLayout.cidr,AllowedipsLayout.bit_at_a,AllowedipsLayout.bit_at_b,
    AllowedipsLayout.bitlen,AllowedipsLayout.bits,List.mem_cons,List.not_mem_nil,
    or_false,Prod.mk.injEq] at field
  omega

private theorem subrange {base offset size a} (bound : offset+size≤56)
    (inside : InRange (.ofNat 64 (base+offset)) size a) : InRange (.ofNat 64 base) 56 a := by
  obtain ⟨i,small,eq⟩ := inside
  refine ⟨offset+i,by omega,?_⟩
  simpa only [BitVec.ofNat_add,BitVec.add_assoc] using eq

/-- Publication reconstructs the packed parent and physical root word while
preserving the initialized record. The root-slot separation is the ordinary
table/allocation resource fact, not a postcondition supplied by a service. -/
theorem publish_node {names : Names} {s : MachineData} {before after : DataMem}
    {id slot : Nat} {node : Trie.Node} {parentSlot : Slot}
    (extent : s.regs.rbx.toNat+56≤2^64) (slotExtent : slot+8≤2^64)
    (core : Trie.decodeNode names.trie nodeOffsets before s.regs.rbx.toNat=.ok node)
    (saved : word before "root.slot" (s.regs.rsp.toNat+8) 8=.ok slot)
    (root : parent names (slot ||| 2)=.ok parentSlot)
    (apart : ∀ a, InRange s.regs.rbx.toBitVec 56 a → ¬InRange (.ofNat 64 slot) 8 a)
    (checked : publish s before=.ok after) :
    decodeNode names nodeOffsets after id s.regs.rbx.toNat=
      .ok (id,({peer:=node.peer,bit:=node.children,cidr:=node.cidr,bitlen:=node.width,bits:=node.key,parent:=parentSlot} : AipNode)) ∧
    word after "table.root" slot 8=.ok s.regs.rbx.toNat := by
  unfold publish at checked
  obtain ⟨raw,read,checked⟩ := bind_ok checked
  obtain ⟨middle,parentStore,rootStore⟩ := bind_ok checked
  have equal : raw=slot :=
    Int.ofNat.inj (Option.some.inj ((Trie.readNat_loadInt read).symm.trans (word_loadInt _ _ _ _ _ saved)))
  subst raw
  have middleEq := (store_facts parentStore).2
  have afterEq := (store_facts rootStore).2
  have rootFrame : EqualOutside (InRange (.ofNat 64 slot) 8) middle after := by
    rw [afterEq]; exact storeInt_frame _ _ _ _
  have keep (offset size : Nat) (bound : offset+size≤56) (path : String) :
      word after path (s.regs.rbx.toNat+offset) size=word middle path (s.regs.rbx.toNat+offset) size := by
    apply (Trie.word_frame rootFrame path _ _ _).symm
    intro a inside
    apply apart a
    simpa only [ofNat_uint64] using subrange bound inside
  have coreSame : Trie.decodeNode names.trie nodeOffsets after s.regs.rbx.toNat=
      Trie.decodeNode names.trie nodeOffsets before s.regs.rbx.toNat := by
    apply Trie.decodeNode_congr
    intro offset size field path
    have within := core_field_within field
    rw [keep offset size (by omega) path,middleEq]
    exact word_store_frame before path s.regs.rbx.toNat offset size 48 8 _
      (by omega) (by decide) (.inl within)
  have parentRead : word after "node.parent" (s.regs.rbx.toNat+48) 8=.ok (slot ||| 2) := by
    rw [keep 48 8 (by decide) "node.parent",middleEq]
    exact word_store_same _ _ _ _ _ extent
      (Nat.or_lt_two_pow (by simpa using word_bound saved) (by decide))
  refine ⟨?_,?_⟩
  · simp only [decodeNode,coreSame,core,AllowedipsMutationLayout.parent_bit_packed,parentRead,root,ok_bind]
    rfl
  · rw [afterEq]
    exact word_store_same _ _ _ _ _ slotExtent s.regs.rbx.toBitVec.isLt

#print axioms publish_node
end Binary.Pair.Allowedips.Root
