import AllowedipsChildPublishRegions

namespace Binary.Pair.Allowedips.ChildPublish
open AllowedipsMutationImage Root
local instance : Labels := Image.linkedLabels

theorem read_word8 {s a n} (read : readNat s a 1=.ok n) :
    n<256 ∧ s.data.dmem.loadInt (.ofNat 64 a) 1=some ((BitVec.ofNat 8 n).toNat : Int) := by
  have loaded := Trie.readNat_loadInt read
  have bound := (loadInt_range _ _ _ _ loaded).2
  change (n : Int)<256 at bound
  refine ⟨by omega,?_⟩
  simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : n<2^8)] using loaded

/-- Both publication stores and the intervening saved-index read follow the
tested summary. No disjointness or child-index bound is needed here; the
surrounding trie invariant establishes that this is a valid child slot. -/
theorem effect_segment (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    {s : MachineData} {memory : DataMem} {registers : Reg64s}
    (checked : effect s=.ok (memory,registers)) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=Add.entry+0x549 ∧ t.data.dmem=memory ∧ t.data.regs=registers)
      ⟨s,Add.entry+0x6f2⟩ := by
  unfold effect at checked
  obtain ⟨direction,directionRead,checked⟩ := bind_ok checked
  obtain ⟨base,baseRead,checked⟩ := bind_ok checked
  obtain ⟨middle,parentStore,checked⟩ := bind_ok checked
  obtain ⟨index,indexRead,checked⟩ := bind_ok checked
  obtain ⟨last,linkStore,checked⟩ := bind_ok checked
  cases Except.ok.inj checked
  obtain ⟨small,directionLoad⟩ := read_word8 directionRead
  have directionNat : (BitVec.ofNat 8 direction).toNat=direction :=
    Nat.mod_eq_of_lt small
  have directionWord : (BitVec.ofNat 8 direction).setWidth 64=BitVec.ofNat 64 direction :=
    BitVec.setWidth_ofNat_of_le_of_lt (by decide) small
  obtain ⟨parentMapped,parentEq⟩ := store_facts parentStore
  obtain ⟨linkMapped,linkEq⟩ := store_facts linkStore
  rw [store_unsigned] at parentEq
  rw [store_nat64] at linkEq
  have first := prepare s (.ofNat 8 direction) (.ofNat 64 base)
    (by simpa [BitVec.ofNat_add,ofNat_uint64] using directionLoad)
    (by simpa [ofNat_uint64] using Exact.read_word64 baseRead)
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually ((AllowedipsLoop.layout_take Add_r6f2_layout 4).agreement decoder.add) s _ first)
  rintro a ⟨pcA,memA,regsA⟩
  have slotA : slot a.data=s.regs.rbx.toBitVec+.ofNat 64 (((direction+1)%256)*8) := by
    simp [slot,regsA,directionNat,UInt64.toBitVec_ofNat',BitVec.ofNat_mul]
  have packedA : packed a.data=(s.regs.rbx.toBitVec+.ofNat 64 (((direction+1)%256)*8)) ||| .ofNat 64 direction := by
    simp only [packed,slotA,regsA,directionWord]
    exact BitVec.or_comm _ _
  have memoryA : parentMemory a.data=middle := by
    rw [parentMemory,memA,packedA]
    simpa [regsA,BitVec.ofNat_add] using parentEq.symm
  have second := parent_store a.data (.ofNat 64 index)
    (by simpa [memA,regsA,BitVec.ofNat_add] using parentMapped)
    (by simpa [memoryA,regsA,BitVec.ofNat_add,ofNat_uint64] using Exact.read_word64 indexRead)
  have secondLayout : LaidOut Add.fetch (Add.entry+0x701) (Add.r6f2.drop 4) := by binary_layout
  rw [Placement.at_pc a _ pcA]
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (secondLayout.agreement decoder.add) a.data _ second)
  rintro b ⟨pcB,memB,regsB⟩
  have final := child_store b.data
    (by simpa [memB,memoryA,regsB,regsA,BitVec.ofNat_add,BitVec.ofNat_mul,ofNat_uint64] using linkMapped)
  rw [Placement.at_pc b _ pcB]
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (region_eventually (Add_r711_layout.agreement decoder.add) b.data _ final)
  rintro t ⟨pcT,memT,regsT⟩
  refine ⟨pcT,?_,?_⟩
  · rw [memT]
    simpa [memB,memoryA,regsB,regsA,BitVec.ofNat_add,BitVec.ofNat_mul,ofNat_uint64] using linkEq.symm
  · simp only [regsT,regsB,slotA,packedA,regsA]
    rfl

#print axioms effect_segment
end Binary.Pair.Allowedips.ChildPublish
