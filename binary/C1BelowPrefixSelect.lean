import AllowedipsSelectTotal
import AllowedipsSelectChecked

/-! Result C1, work package 3, prefix: the post-initialization selector
(`add+0x212`) when the placed node's slot on the key's side is occupied.
The landed `Select.empty_total` covers the empty slot (child attachment);
this is its analogue for the paths below the placement. -/
namespace Binary.Pair.Allowedips.Select
open Root AllowedipsChild AllowedipsRelation

private theorem ok_bind' (value : α) (f : α → Except ε β) :
    ((Except.ok value : Except ε α) >>= f)=f value := rfl

private theorem read_loaded' {s : MachineData} {address size value : Nat}
    (loaded : s.dmem.loadInt (.ofNat 64 address) size=some (value : Int)) :
    readNat ⟨s,0⟩ address size=.ok value := by
  obtain ⟨actual,read⟩ := readNat_exists (s:=⟨s,0⟩) (Option.isSome_of_eq_some loaded)
  have equal : actual=value := Int.ofNat.inj (Option.some.inj ((Trie.readNat_loadInt read).symm.trans loaded))
  exact equal ▸ read

/-- A resolved non-NULL pointer is the address of a named node. -/
theorem pointer_some_named {names : List (Nat × Nat)} {path raw id}
    (decoded : Trie.pointer names path raw=.ok (some id)) : raw≠0 ∧ (id,raw) ∈ names := by
  unfold Trie.pointer at decoded
  split at decoded
  · cases decoded
  · rename_i nonzero
    split at decoded
    · rename_i found address searched
      cases decoded
      have member := List.mem_of_find?_eq_some searched
      have same := List.find?_some searched
      have equal : address=raw := eq_of_beq same
      subst equal
      exact ⟨fun zero => nonzero (by simp [zero]),member⟩
    · cases decoded

/-- A decoded occupied child and the actual query/saved words derive the
selector's summary with the nonempty exit `add+0x241`: the stack word
receives the child's address, which is the address of a named node. -/
theorem occupied_total {names : Trie.Names} {s : MachineData} {node : Trie.Node} {key base childId : Nat}
    (decoded : Trie.decodeNode names nodeOffsets s.dmem s.regs.rbx.toNat=.ok node)
    (query : QueryWords s.dmem s.regs.r13.toBitVec node.width key)
    (short : node.cidr<node.width)
    (occupied : node.children[key/2^(node.width-1-node.cidr)%2]?=some (some childId))
    (saved : readNat ⟨s,0⟩ (s.regs.rsp.toNat+24) 8=.ok base)
    (mapped : (s.dmem.loadInt s.regs.rsp.toBitVec 8).isSome=true) :
    ∃ child, child≠0 ∧ (childId,child) ∈ names.nodes ∧
      effect s=.ok (s.dmem.storeInt s.regs.rsp.toBitVec 8 child,
        {s.regs with
          rax:=.ofNat (key/2^(node.width-1-node.cidr)%2),rdx:=.ofNat (key/2^(node.width-1-node.cidr)%2),
          rcx:=.ofNat child,r8:=.ofNat base},0x241) := by
  have fields := Trie.decodeNode_fields decoded
  let ix := byteSelector node.width node.cidr
  let shift := 7-node.cidr%8
  let byte := queryByte node.width key ix
  let direction := key/2^(node.width-1-node.cidr)%2
  have indexRead : readNat ⟨s,0⟩ (s.regs.rbx.toNat+25) 1=.ok ix := readNat_of_word fields.byteSelector
  have shiftRead : readNat ⟨s,0⟩ (s.regs.rbx.toNat+26) 1=.ok shift := readNat_of_word fields.bitSelector
  have position := selector_position node.width node.cidr fields.family short
  have byteRead : readNat ⟨s,0⟩ (s.regs.r13.toNat+ix) 1=.ok byte := by
    apply read_loaded'
    simpa only [BitVec.ofNat_add,ofNat_uint64,ix,byte] using
      queryByte_read _ _ _ _ _ fields.family position.2 query
  have chosen : byte/2^shift%2=direction := queryByte_select _ _ _ fields.family short
  have bounds : ix<16 ∧ shift<8 := by
    have family := fields.family
    dsimp only [shift]
    change byteSelector node.width node.cidr<16 ∧ _
    rcases family with family|family <;> rw [family] at position ⊢ <;> omega
  obtain ⟨left,right,lp,rp,shape,leftRead,leftPointer,rightRead,rightPointer⟩ := fields.children
  rw [shape] at occupied
  have childRead : ∃ child, child≠0 ∧ (childId,child) ∈ names.nodes ∧
      readNat ⟨s,0⟩ (s.regs.rbx.toNat+8+direction*8) 8=.ok child := by
    have cases : direction=0 ∨ direction=1 := by dsimp only [direction]; omega
    rcases cases with zero|one
    · have present : left=some childId := by
        simpa [←show direction=key/2^(node.width-1-node.cidr)%2 from rfl,zero] using occupied
      obtain ⟨nonzero,named⟩ := pointer_some_named (present ▸ leftPointer)
      refine ⟨lp,nonzero,named,?_⟩
      simpa only [readNat,zero,Nat.zero_mul,Nat.mul_zero,Nat.add_zero] using
        (readNat_of_word leftRead : readNat ⟨s,0⟩ (s.regs.rbx.toNat+8+8*0) 8=.ok lp)
    · have present : right=some childId := by
        simpa [←show direction=key/2^(node.width-1-node.cidr)%2 from rfl,one] using occupied
      obtain ⟨nonzero,named⟩ := pointer_some_named (present ▸ rightPointer)
      refine ⟨rp,nonzero,named,?_⟩
      simpa only [readNat,one,Nat.one_mul,Nat.mul_one] using
        (readNat_of_word rightRead : readNat ⟨s,0⟩ (s.regs.rbx.toNat+8+8*1) 8=.ok rp)
  obtain ⟨child,nonzero,named,childRead⟩ := childRead
  have stored := store_total (memory:=s.dmem) (address:=s.regs.rsp.toNat) (size:=8) (value:=child)
    (by simpa only [ofNat_uint64] using mapped)
  have stored : store s.dmem s.regs.rsp.toNat 8 child=.ok (s.dmem.storeInt s.regs.rsp.toBitVec 8 child) := by
    simpa [ofNat_uint64] using stored
  have selectors : (decide (ix<16) && decide (shift<8))=true := by
    simp only [bounds.1,bounds.2,decide_true,Bool.true_and]
  refine ⟨child,nonzero,named,?_⟩
  simp only [effect,indexRead,shiftRead,saved,byteRead,chosen,selectors,
    require,ite_true,childRead,stored,ok_bind',nonzero,ite_false]
  rfl

#print axioms occupied_total
end Binary.Pair.Allowedips.Select
