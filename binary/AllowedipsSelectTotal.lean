import AllowedipsSelectLocals

namespace Binary.Pair.Allowedips.Select
open Root AllowedipsChild AllowedipsRelation

private theorem ok_bind (value : α) (f : α → Except ε β) :
    ((Except.ok value : Except ε α) >>= f)=f value := rfl

private theorem read_loaded {s : MachineData} {address size value : Nat}
    (loaded : s.dmem.loadInt (.ofNat 64 address) size=some (value : Int)) :
    readNat ⟨s,0⟩ address size=.ok value := by
  obtain ⟨actual,read⟩ := readNat_exists (s:=⟨s,0⟩) (Option.isSome_of_eq_some loaded)
  have equal : actual=value := Int.ofNat.inj (Option.some.inj ((Trie.readNat_loadInt read).symm.trans loaded))
  exact equal ▸ read

private theorem pointer_none_zero {names path raw}
    (decoded : Trie.pointer names path raw=.ok none) : raw=0 := by
  unfold Trie.pointer at decoded
  split at decoded
  · exact eq_of_beq (by assumption)
  · split at decoded <;> cases decoded

/-- A decoded empty child and the actual query/saved words derive successful
selection. Neither a future state nor an assumed successful summary is needed. -/
theorem empty_total {names : Trie.Names} {s : MachineData} {node : Trie.Node} {key base : Nat}
    (decoded : Trie.decodeNode names nodeOffsets s.dmem s.regs.rbx.toNat=.ok node)
    (query : QueryWords s.dmem s.regs.r13.toBitVec node.width key)
    (short : node.cidr<node.width)
    (empty : node.children[key/2^(node.width-1-node.cidr)%2]?=some none)
    (saved : readNat ⟨s,0⟩ (s.regs.rsp.toNat+24) 8=.ok base)
    (mapped : (s.dmem.loadInt s.regs.rsp.toBitVec 8).isSome=true) :
    ∃ memory registers, effect s=.ok (memory,registers,0x6e0) ∧
      (s.dmem.loadInt (.ofNat 64
        (s.regs.rbx.toNat+(key/2^(node.width-1-node.cidr)%2)*8+8)) 8).isSome=true := by
  have fields := Trie.decodeNode_fields decoded
  let ix := byteSelector node.width node.cidr
  let shift := 7-node.cidr%8
  let byte := queryByte node.width key ix
  let direction := key/2^(node.width-1-node.cidr)%2
  have indexRead : readNat ⟨s,0⟩ (s.regs.rbx.toNat+25) 1=.ok ix := readNat_of_word fields.byteSelector
  have shiftRead : readNat ⟨s,0⟩ (s.regs.rbx.toNat+26) 1=.ok shift := readNat_of_word fields.bitSelector
  have position := selector_position node.width node.cidr fields.family short
  have byteRead : readNat ⟨s,0⟩ (s.regs.r13.toNat+ix) 1=.ok byte := by
    apply read_loaded
    simpa only [BitVec.ofNat_add,ofNat_uint64,ix,byte] using
      queryByte_read _ _ _ _ _ fields.family position.2 query
  have chosen : byte/2^shift%2=direction := queryByte_select _ _ _ fields.family short
  have bounds : ix<16 ∧ shift<8 := by
    have family := fields.family
    dsimp only [shift]
    change byteSelector node.width node.cidr<16 ∧ _
    rcases family with family|family <;> rw [family] at position ⊢ <;> omega
  obtain ⟨left,right,lp,rp,shape,leftRead,leftPointer,rightRead,rightPointer⟩ := fields.children
  rw [shape] at empty
  have childRead : readNat ⟨s,0⟩ (s.regs.rbx.toNat+8+direction*8) 8=.ok 0 := by
    have cases : direction=0 ∨ direction=1 := by dsimp only [direction]; omega
    rcases cases with zero|one
    · have absent : left=none := by simpa [←show direction=key/2^(node.width-1-node.cidr)%2 from rfl,zero] using empty
      have raw : lp=0 := pointer_none_zero (absent ▸ leftPointer)
      rw [raw] at leftRead
      simpa only [readNat,zero,Nat.zero_mul,Nat.mul_zero,Nat.add_zero] using
        (readNat_of_word leftRead : readNat ⟨s,0⟩ (s.regs.rbx.toNat+8+8*0) 8=.ok 0)
    · have absent : right=none := by simpa [←show direction=key/2^(node.width-1-node.cidr)%2 from rfl,one] using empty
      have raw : rp=0 := pointer_none_zero (absent ▸ rightPointer)
      rw [raw] at rightRead
      simpa only [readNat,one,Nat.one_mul,Nat.mul_one] using
        (readNat_of_word rightRead : readNat ⟨s,0⟩ (s.regs.rbx.toNat+8+8*1) 8=.ok 0)
  let memory := s.dmem.storeInt s.regs.rsp.toBitVec 8 0
  have stored := store_total (memory:=s.dmem) (address:=s.regs.rsp.toNat) (size:=8) (value:=0)
    (by simpa only [ofNat_uint64] using mapped)
  have stored : store s.dmem s.regs.rsp.toNat 8 0=.ok memory := by
    simpa [ofNat_uint64,memory] using stored
  have selectors : (decide (ix<16) && decide (shift<8))=true := by simp only [bounds.1,bounds.2,decide_true,Bool.true_and]
  refine ⟨memory,{s.regs with
    rax:=.ofNat direction,rdx:=.ofNat direction,rcx:=0,r8:=.ofNat base},?_,?_⟩
  · simp only [effect,indexRead,shiftRead,saved,byteRead,chosen,selectors,
      require,ite_true,childRead,stored,ok_bind]
    rfl
  · have loaded := Trie.readNat_loadInt childRead
    rw [Nat.add_right_comm] at loaded
    exact Option.isSome_of_eq_some loaded

#print axioms empty_total
end Binary.Pair.Allowedips.Select
