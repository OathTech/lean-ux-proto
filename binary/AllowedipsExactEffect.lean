import AllowedipsExactRegions
import PairLocalsProof
import AllowedipsPlacementPrefix

namespace Binary.Pair.Allowedips.Exact
open AllowedipsMutationImage TrustBase
local instance : Labels := Image.linkedLabels

private theorem word_bound_nat (n : Nat) (bound : (n : Int)<18446744073709551616) : n<2^64 := by omega

/-- Decode a machine word without introducing an unbounded integer premise. -/
theorem read_word64 {s a n} (read : readNat s a 8=.ok n) :
    s.data.dmem.loadInt (.ofNat 64 a) 8=some ((BitVec.ofNat 64 n).toNat : Int) := by
  have loaded := Trie.readNat_loadInt read
  have bound := (loadInt_range _ _ _ _ loaded).2
  change (n : Int)<18446744073709551616 at bound
  simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (word_bound_nat n bound)] using loaded

theorem removeEffect_run {s memory regs} (checked : removeEffect s=.ok (memory,regs)) :
    (Placement.physical Add.r3e5 0x3e5 s).All (fun t =>
      t.pc=Add.entry+0x406 ∧ t.data.dmem=memory ∧ t.data.regs=regs) := by
  unfold removeEffect at checked
  obtain ⟨previous,back,checked⟩ := bind_ok checked
  obtain ⟨next,forward,checked⟩ := bind_ok checked
  obtain ⟨_,ownerMapped,checked⟩ := bind_ok checked
  obtain ⟨_,nextMapped,checked⟩ := bind_ok checked
  obtain ⟨_,previousMapped,checked⟩ := bind_ok checked
  obtain ⟨last,tail,checked⟩ := bind_ok checked
  cases Except.ok.inj checked
  apply remove s (.ofNat 64 previous) (.ofNat 64 next) (.ofNat 64 last)
  · simpa only [BitVec.ofNat_add,show BitVec.ofNat 64 64=(64 : BitVec 64) from rfl,
      (Trie.u64_of_nat (rfl : s.regs.rbx.toNat=s.regs.rbx.toNat)).symm] using read_word64 back
  · simpa only [BitVec.ofNat_add,show BitVec.ofNat 64 56=(56 : BitVec 64) from rfl,
      (Trie.u64_of_nat (rfl : s.regs.rbx.toNat=s.regs.rbx.toNat)).symm] using read_word64 forward
  · exact require_ok ownerMapped
  · exact require_ok nextMapped
  · exact require_ok previousMapped
  · simpa only [BitVec.ofNat_add,show BitVec.ofNat 64 1104=(1104 : BitVec 64) from rfl,
      (Trie.u64_of_nat (rfl : s.regs.r14.toNat=s.regs.r14.toNat)).symm] using read_word64 tail

theorem appendEffect_run {s memory regs} (checked : appendEffect s=.ok (memory,regs)) :
    (Placement.physical Add.r406 0x406 s).All (fun t =>
      t.pc=Add.entry+0x549 ∧ t.data.dmem=memory ∧ t.data.regs=regs) := by
  unfold appendEffect at checked
  obtain ⟨_,head,checked⟩ := bind_ok checked
  obtain ⟨_,forward,checked⟩ := bind_ok checked
  obtain ⟨_,back,checked⟩ := bind_ok checked
  obtain ⟨_,last,checked⟩ := bind_ok checked
  cases Except.ok.inj checked
  exact append s (require_ok head) (require_ok forward) (require_ok back) (require_ok last)

theorem appendEffect_congr {s t : MachineData} (memory : s.dmem=t.dmem) (regs : s.regs=t.regs) :
    appendEffect s=appendEffect t := by
  simp only [appendEffect,headMemory,forwardMemory,backwardMemory,addedMemory,memory,regs]

/-- The paired runner's exact memory/register effect is realized by every
execution of the complete callback-free binary segment. No mutation effect
or list correspondence is assumed in the instruction semantics. -/
theorem effect_segment (fetch : Int64 → Option Decoded) (decoder : AllowedipsMutationDecoderAgreement fetch)
    {s memory regs} (checked : effect s=.ok (memory,regs)) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=Add.entry+0x549 ∧ t.data.dmem=memory ∧ t.data.regs=regs) ⟨s,Add.entry+0x3e5⟩ := by
  unfold effect at checked
  obtain ⟨⟨middle,registers⟩,removeCheck,appendCheck⟩ := bind_ok checked
  have first := region_eventually (Add_r3e5_layout.agreement decoder.add) s _ (removeEffect_run removeCheck)
  apply eventually_trans (instructionStep fetch) _ _ _ first
  rintro t ⟨pc,memoryEq,regsEq⟩
  have same : appendEffect t.data=appendEffect {s with dmem := middle,regs := registers} :=
    appendEffect_congr memoryEq regsEq
  rw [Placement.at_pc t _ pc]
  exact region_eventually (Add_r406_layout.agreement decoder.add) t.data _
    (appendEffect_run (same.trans appendCheck))

#print axioms effect_segment
end Binary.Pair.Allowedips.Exact
