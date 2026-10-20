import AllowedipsSelectChecked
import AllowedipsRootRecord

namespace Binary.Pair.Allowedips.Select
open AllowedipsChild AllowedipsRelation Root

private theorem read_word_agrees {s : MachineData} {address size actual expected path}
    (read : readNat ⟨s,0⟩ address size=.ok actual)
    (decoded : word s.dmem path address size=.ok expected) : actual=expected :=
  Int.ofNat.inj (Option.some.inj ((Trie.readNat_loadInt read).symm.trans
    (word_loadInt _ _ _ _ _ decoded)))

/-- The machine selector is the mirror's key bit, derived from the decoded
parent's selector bytes and the query's actual words. No direction is supplied
by a test oracle or added to the reconstruction. -/
theorem selected_key {names : Trie.Names} {s : MachineData} {node : Trie.Node}
    {key : Nat} {memory : DataMem} {registers : Reg64s} {offset : Nat}
    (decoded : Trie.decodeNode names nodeOffsets s.dmem s.regs.rbx.toNat=.ok node)
    (query : QueryWords s.dmem s.regs.r13.toBitVec node.width key)
    (short : node.cidr<node.width) (checked : effect s=.ok (memory,registers,offset)) :
    registers.rax.toNat=key/2^(node.width-1-node.cidr)%2 ∧
    registers.rdx.toNat=key/2^(node.width-1-node.cidr)%2 := by
  unfold effect at checked
  obtain ⟨byteIndex,indexRead,checked⟩ := bind_ok checked
  obtain ⟨shift,shiftRead,checked⟩ := bind_ok checked
  obtain ⟨base,_,checked⟩ := bind_ok checked
  obtain ⟨byte,byteRead,checked⟩ := bind_ok checked
  obtain ⟨_,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨child,_,checked⟩ := bind_ok checked
  obtain ⟨_,_,checked⟩ := bind_ok checked
  cases Except.ok.inj checked
  have fields := Trie.decodeNode_fields decoded
  have ix := read_word_agrees indexRead fields.byteSelector
  have sh := read_word_agrees shiftRead fields.bitSelector
  have byteRead := Trie.readNat_loadInt byteRead
  rw [ix] at byteRead
  have loaded := queryByte_read s.dmem s.regs.r13.toBitVec node.width key
    (byteSelector node.width node.cidr) fields.family
    (selector_position node.width node.cidr fields.family short).2 query
  have actual : byte=queryByte node.width key (byteSelector node.width node.cidr) := by
    apply Int.ofNat.inj
    apply Option.some.inj
    apply byteRead.symm.trans
    simpa only [byteSelector,BitVec.ofNat_add,ofNat_uint64,Int.ofNat_eq_natCast] using loaded
  have selectedEq : byte/2^shift%2=key/2^(node.width-1-node.cidr)%2 := by
    rw [actual,sh]
    exact queryByte_select node.width key node.cidr fields.family short
  have bounded : byte/2^shift%2<2^64 := by omega
  have reduced : (UInt64.ofNat (byte/2^shift%2)).toNat=byte/2^shift%2 :=
    UInt64.toNat_ofNat_of_lt' bounded
  exact ⟨reduced.trans selectedEq,reduced.trans selectedEq⟩

#print axioms selected_key
end Binary.Pair.Allowedips.Select
