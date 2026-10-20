import AllowedipsSelectKey

namespace Binary.Pair.Allowedips.Select
open AllowedipsChild Root

private theorem read_agrees {s : MachineData} {address size actual expected path}
    (read : readNat ⟨s,0⟩ address size=.ok actual)
    (decoded : word s.dmem path address size=.ok expected) : actual=expected :=
  Int.ofNat.inj (Option.some.inj ((Trie.readNat_loadInt read).symm.trans (word_loadInt _ _ _ _ _ decoded)))

/-- Taking the compiled empty-child edge establishes the mirror's empty slot,
using the same decoded parent and selected query bit as the runtime summary. -/
theorem empty_selected_slot {names : Trie.Names} {s : MachineData} {node : Trie.Node}
    {key : Nat} {memory : DataMem} {registers : Reg64s}
    (decoded : Trie.decodeNode names nodeOffsets s.dmem s.regs.rbx.toNat=.ok node)
    (query : QueryWords s.dmem s.regs.r13.toBitVec node.width key)
    (short : node.cidr<node.width) (checked : effect s=.ok (memory,registers,0x6e0)) :
    node.children[key/2^(node.width-1-node.cidr)%2]?=some none := by
  have directionEq := (selected_key decoded query short checked).1
  unfold effect at checked
  obtain ⟨byteIndex,_,checked⟩ := bind_ok checked
  obtain ⟨shift,_,checked⟩ := bind_ok checked
  obtain ⟨base,_,checked⟩ := bind_ok checked
  obtain ⟨byte,_,checked⟩ := bind_ok checked
  obtain ⟨_,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨child,childRead,checked⟩ := bind_ok checked
  obtain ⟨_,_,checked⟩ := bind_ok checked
  have result := Except.ok.inj checked
  have exit := congrArg (fun value : DataMem×Reg64s×Nat => value.2.2) result
  have childZero : child=0 := by
    by_cases empty : child=0
    · exact empty
    · simp only [empty,ite_false] at exit
      contradiction
  have registersEq := congrArg (fun value : DataMem×Reg64s×Nat => value.2.1) result
  dsimp only at registersEq
  rw [←registersEq] at directionEq
  have reduced : (UInt64.ofNat (byte/2^shift%2)).toNat=byte/2^shift%2 :=
    UInt64.toNat_ofNat_of_lt' (by change byte/2^shift%2<2^64; omega)
  change (UInt64.ofNat (byte/2^shift%2)).toNat=key/2^(node.width-1-node.cidr)%2 at directionEq
  rw [reduced] at directionEq
  rw [directionEq,childZero] at childRead
  obtain ⟨left,right,lp,rp,shape,leftRead,leftPointer,rightRead,rightPointer⟩ := (Trie.decodeNode_fields decoded).children
  rw [show nodeOffsets.children=8 from rfl] at leftRead rightRead
  have which : key/2^(node.width-1-node.cidr)%2=0 ∨ key/2^(node.width-1-node.cidr)%2=1 := by omega
  rcases which with direction|direction
  · rw [direction] at childRead ⊢
    have zero : lp=0 := (read_agrees childRead (by simpa only [Nat.zero_mul,Nat.add_zero] using leftRead)).symm
    rw [zero] at leftPointer
    have equal : left=none := (Except.ok.inj leftPointer).symm
    simp only [shape,equal]
    rfl
  · rw [direction] at childRead ⊢
    have zero : rp=0 := (read_agrees childRead (by simpa only [Nat.one_mul] using rightRead)).symm
    rw [zero] at rightPointer
    have equal : right=none := (Except.ok.inj rightPointer).symm
    simp only [shape,equal]
    rfl

#print axioms empty_selected_slot

local instance : Labels := Image.linkedLabels

theorem selection_checked (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    {names : Trie.Names} {s : MachineData} {node : Trie.Node}
    {key : Nat} {memory : DataMem} {registers : Reg64s} {offset : Nat}
    (decoded : Trie.decodeNode names nodeOffsets s.dmem s.regs.rbx.toNat=.ok node)
    (query : QueryWords s.dmem s.regs.r13.toBitVec node.width key)
    (short : node.cidr<node.width) (checked : effect s=.ok (memory,registers,offset)) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=AllowedipsMutationImage.Add.entry+.ofNat offset ∧ t.data.dmem=memory ∧ t.data.regs=registers ∧
      EqualOutside (InRange s.regs.rsp.toBitVec 8) s.dmem t.data.dmem ∧ MappedLe s.dmem t.data.dmem ∧
      t.data.regs.rax.toNat=key/2^(node.width-1-node.cidr)%2 ∧
      t.data.regs.rdx.toNat=key/2^(node.width-1-node.cidr)%2 ∧
      (offset=0x6e0 → node.children[key/2^(node.width-1-node.cidr)%2]?=some none))
      ⟨s,AllowedipsMutationImage.Add.entry+0x212⟩ := by
  have direction := selected_key decoded query short checked
  apply eventually_weaken (instructionStep fetch) _ _ _ _ (effect_segment fetch decoder checked)
  rintro t ⟨pc,mem,regs,frame,mapped⟩
  refine ⟨pc,mem,regs,frame,mapped,regs ▸ direction.1,regs ▸ direction.2,?_⟩
  intro empty
  subst offset
  exact empty_selected_slot decoded query short checked

#print axioms selection_checked
end Binary.Pair.Allowedips.Select
