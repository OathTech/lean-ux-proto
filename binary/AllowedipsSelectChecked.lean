import AllowedipsSelectRegions
import AllowedipsRootStore
import PairMappedMemory

namespace Binary.Pair.Allowedips.Select
open AllowedipsMutationImage AllowedipsChild Root
local instance : Labels := Image.linkedLabels

/-- Both child-selection exits follow the same executable summary used by the
paired runner. Its sole write saves the selected child in the stack word. -/
theorem effect_segment (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    {s : MachineData} {memory : DataMem} {registers : Reg64s} {offset : Nat}
    (checked : effect s=.ok (memory,registers,offset)) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=Add.entry+.ofNat offset ∧ t.data.dmem=memory ∧ t.data.regs=registers ∧
      EqualOutside (InRange s.regs.rsp.toBitVec 8) s.dmem t.data.dmem ∧ MappedLe s.dmem t.data.dmem)
      ⟨s,Add.entry+0x212⟩ := by
  unfold effect at checked
  obtain ⟨byteIndex,indexRead,checked⟩ := bind_ok checked
  obtain ⟨shift,shiftRead,checked⟩ := bind_ok checked
  obtain ⟨base,baseRead,checked⟩ := bind_ok checked
  obtain ⟨byte,byteRead,checked⟩ := bind_ok checked
  obtain ⟨selectors,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨child,childRead,checked⟩ := bind_ok checked
  obtain ⟨last,stored,checked⟩ := bind_ok checked
  cases Except.ok.inj checked
  have bounds : byteIndex<16 ∧ shift<8 := by simpa using selectors
  have byteBound : byte<256 := by
    have upper := (loadInt_range _ _ _ _ (Trie.readNat_loadInt byteRead)).2
    change (byte : Int)<256 at upper
    omega
  have childBound : child<2^64 := by
    have upper := (loadInt_range _ _ _ _ (Trie.readNat_loadInt childRead)).2
    change (child : Int)<18446744073709551616 at upper
    change child<18446744073709551616
    omega
  obtain ⟨mapped,memoryEq⟩ := store_facts stored
  rw [store_nat64] at memoryEq
  have memoryEq : memory=s.dmem.storeInt s.regs.rsp.toBitVec 8 (BitVec.ofNat 64 child).toInt := by
    simpa only [ofNat_uint64] using memoryEq
  obtain ⟨old,mapped⟩ := Option.isSome_iff_exists.mp mapped
  have physical := select_step s byteIndex shift byte (.ofNat 64 base) (.ofNat 64 child)
    bounds.1 bounds.2 byteBound old (by simpa only [ofNat_uint64] using mapped)
    (by simpa [BitVec.ofNat_add,ofNat_uint64] using Trie.readNat_loadInt indexRead)
    (by simpa [BitVec.ofNat_add,ofNat_uint64] using Trie.readNat_loadInt shiftRead)
    (by simpa [BitVec.ofNat_add,ofNat_uint64] using Exact.read_word64 baseRead)
    (by simpa [BitVec.ofNat_add,ofNat_uint64] using Trie.readNat_loadInt byteRead)
    (by simpa [BitVec.ofNat_add,ofNat_uint64,selected,Nat.mul_comm] using Exact.read_word64 childRead)
  have layout : LaidOut Add.fetch (Add.entry+0x212) (Add.r212++Add.r231) := by binary_layout
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (region_eventually (layout.agreement decoder.add) s _ physical)
  rintro t ⟨pc,mem,regs⟩
  refine ⟨?_,mem.trans memoryEq.symm,?_,?_,?_⟩
  · have zero : BitVec.ofNat 64 child=0 ↔ child=0 := by
      constructor
      · intro same
        have equal := congrArg BitVec.toNat same
        simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt childBound] at equal
        exact equal.trans rfl
      · intro same; subst child; rfl
    rw [pc]
    by_cases empty : child=0
    · rw [ite_eq_left (zero.mpr empty),ite_eq_left empty]; rfl
    · rw [ite_eq_right (fun same => empty (zero.mp same)),ite_eq_right empty]; rfl
  · have cast (n : Nat) : UInt64.ofBitVec (.ofNat 64 n)=UInt64.ofNat n :=
      UInt64.toBitVec_inj.mp (UInt64.toBitVec_ofNat' n).symm
    simpa only [selected,cast] using regs
  · rw [mem]
    exact storeInt_frame _ _ _ _
  · rw [mem]
    exact MappedLe.store _ _ _ _

#print axioms effect_segment
end Binary.Pair.Allowedips.Select
