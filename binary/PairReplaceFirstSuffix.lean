import PairReplaceFirstState
import PairReplaceClearRegions
import PairReplaceStoreFrame

namespace Binary.Pair.Replace.First
open TrustBase CommonBitsCoverage Index Callback
local instance : Labels := Image.linkedLabels

theorem successor (fetch : Int64 → Option Decoded) (agree : IndexReplaceDecoderAgreement fetch)
    {n o c initial ra shadow original result s}
    (facts : CallFacts n o c initial ra 5) (core : Core c initial ra true shadow result s)
    (layout : Layout o) (f : ReplaceFocus n o original) (nonzero : f.old.next≠0)
    (newBase : s.regs.rbp.toBitVec=BitVec.ofNat 64 f.base)
    (newLink : s.regs.r12.toBitVec=BitVec.ofNat 64 (f.link+o.next))
    (nextRead : word shadow "new.next" (f.link+o.next) 8=.ok f.old.next)
    (mapped : (shadow.loadInt (.ofNat 64 (f.old.next+o.pprev)) 8).isSome=true) :
    Eventually (guardedStep fetch (StackGuard initial.data.regs.rsp)) (fun t => t.pc=codeEntry+0x5e ∧
      Core c initial ra true (write64 shadow (f.old.next+o.pprev) (f.link+o.next)) result t.data)
      ⟨s,codeEntry+0x56⟩ := by
  obtain ⟨entry,next,fields⟩ := f.old.nextFields nonzero
  have newAddress : s.regs.rbp.toBitVec+8=BitVec.ofNat 64 (f.link+o.next) := by
    rw [newBase,ReplaceFocus.link,layout.hash,layout.next,Nat.add_zero,BitVec.ofNat_add]
    rfl
  have read : s.dmem.loadInt (s.regs.rbp.toBitVec+8) 8=some ((BitVec.ofNat 64 f.old.next).toNat : Int) := by
    rw [newAddress,core.load facts ((f.nextSlot layout).heap layout)]
    simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (word_bound nextRead)] using word_loadInt _ _ _ _ _ nextRead
  have nextAddress : BitVec.ofNat 64 f.old.next+8=BitVec.ofNat 64 (f.old.next+o.pprev) := by
    rw [layout.pprev,BitVec.ofNat_add]; rfl
  obtain ⟨value,mappedRead⟩ := Option.isSome_iff_exists.mp mapped
  have actual : s.dmem.loadInt (BitVec.ofNat 64 f.old.next+8) 8=some value := by
    rw [nextAddress,core.load facts ((fields.backSlot layout).heap layout),mappedRead]
  have region := region_guarded (outer := initial.data.regs.rsp) (IndexMutatorImage.Replace_r56_layout.agreement agree) s _ (by rw [core.stack]; stack_path)
    (successor_store s (.ofNat 64 f.old.next) value read actual)
  apply eventually_weaken (guardedStep fetch (StackGuard initial.data.regs.rsp)) _ _ _ _ region
  rintro t ⟨registers,memory,pc⟩
  have step := core.store facts _ 8 (BitVec.ofNat 64 (f.link+o.next)).toInt ((fields.backSlot layout).heap layout)
  have memoryEq : t.data.dmem=write64 s.dmem (f.old.next+o.pprev) (f.link+o.next) := by
    rw [memory,nextAddress,newLink]
    rfl
  exact ⟨pc,⟨by simpa only [registers] using core.stack,by simpa only [registers] using core.owner,
    by simpa only [registers] using core.new,by simpa only [registers] using core.r13,
    by simpa only [registers] using core.r14,by simpa only [registers] using core.r15,
    by simpa only [memoryEq,write64] using step.memory,by simpa only [memoryEq,write64] using step.frame⟩⟩

theorem clear (fetch : Int64 → Option Decoded) (agree : IndexReplaceDecoderAgreement fetch)
    {n o c initial ra shadow original result s}
    (facts : CallFacts n o c initial ra 5) (core : Core c initial ra true shadow result s)
    (layout : Layout o) (f : UnlinkFocus n o original)
    (nextAddress : s.regs.rbx.toBitVec+8=BitVec.ofNat 64 (f.removed+o.next))
    (backAddress : s.regs.rbx.toBitVec+16=BitVec.ofNat 64 (f.removed+o.pprev))
    (mappedNext : (shadow.loadInt (.ofNat 64 (f.removed+o.next)) 8).isSome=true)
    (mappedBack : (shadow.loadInt (.ofNat 64 (f.removed+o.pprev)) 8).isSome=true) :
    Eventually (guardedStep fetch (StackGuard initial.data.regs.rsp)) (fun t => t.pc=codeEntry+0x81 ∧
      Core c initial ra true
        (write64 (write64 (write64 shadow (f.removed+o.next) 0) (f.removed+o.pprev) 0xdead000000000122)
          (f.removed+o.pprev) 0) result t.data) ⟨s,codeEntry+0x63⟩ := by
  have c1 := core.store facts _ 8 0 ((f.fields.nextSlot layout).heap layout)
  have c2 := c1.store facts _ 8 (0xdead000000000122 : BitVec 64).toInt ((f.fields.backSlot layout).heap layout)
  have c3 := c2.store facts _ 8 0 ((f.fields.backSlot layout).heap layout)
  obtain ⟨next,readNext⟩ := Option.isSome_iff_exists.mp mappedNext
  have actualNext : s.dmem.loadInt (s.regs.rbx.toBitVec+8) 8=some next := by
    rw [nextAddress,core.load facts ((f.fields.nextSlot layout).heap layout),readNext]
  have afterBack : ((shadow.storeInt (.ofNat 64 (f.removed+o.next)) 8 0).loadInt (.ofNat 64 (f.removed+o.pprev)) 8).isSome=true :=
    storeInt_defined _ _ _ _ _ _ mappedBack
  obtain ⟨back,readBack⟩ := Option.isSome_iff_exists.mp afterBack
  have actualBack : (s.dmem.storeInt (s.regs.rbx.toBitVec+8) 8 0).loadInt (s.regs.rbx.toBitVec+16) 8=some back := by
    rw [nextAddress,backAddress,c1.load facts ((f.fields.backSlot layout).heap layout),readBack]
  have region := region_guarded (outer := initial.data.regs.rsp) (IndexMutatorImage.Replace_r63_layout.agreement agree) s _ (by rw [core.stack]; stack_path)
    (clear_stores s next back actualNext actualBack)
  apply eventually_weaken (guardedStep fetch (StackGuard initial.data.regs.rsp)) _ _ _ _ region
  rintro t ⟨registers,memory,pc⟩
  rw [clearedMemory,nextAddress,backAddress] at memory
  exact ⟨pc,⟨by simpa only [registers] using core.stack,by simpa only [registers] using core.owner,
    by simpa only [registers] using core.new,by simpa only [registers] using core.r13,
    by simpa only [registers] using core.r14,by simpa only [registers] using core.r15,
    by simpa only [memory,write64] using c3.memory,by simpa [memory,write64] using c3.frame⟩⟩

#print axioms successor
#print axioms clear
end Binary.Pair.Replace.First
