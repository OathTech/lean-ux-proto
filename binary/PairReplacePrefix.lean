import PairReplaceStoreRegions
import PairReplaceStoreFrame

namespace Binary.Pair.Replace
open Leanux Leanux.WG TrustBase CommonBitsCoverage Index
local instance : Labels := Image.linkedLabels

theorem splice (fetch : Int64 → Option Decoded) (agree : IndexReplaceDecoderAgreement fetch)
    {n o c initial ra shadow result s}
    (facts : CallFacts n o c initial ra 5) (core : Core c initial ra true shadow result s)
    (layout : Layout o) (storage : storageCheck n o=true) (f : ReplaceFocus n o shadow)
    (oldBase : s.regs.rbx.toBitVec=BitVec.ofNat 64 (f.old.removed-o.hash))
    (newBase : s.regs.rbp.toBitVec=BitVec.ofNat 64 f.base)
    (mappedNext : (shadow.loadInt (.ofNat 64 (f.base+8)) 8).isSome=true)
    (mappedIndex : (shadow.loadInt (.ofNat 64 (f.base+28)) 4).isSome=true) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=(if f.old.next=0 then codeEntry+0x5e else codeEntry+0x51) ∧
      Core c initial ra true (replacePrefixMemory shadow o f.link f.old.previous f.old.next f.old.entry.index) result t.data ∧
      t.data.regs.r12=UInt64.ofNat f.link)
      ⟨s,codeEntry+0x2b⟩ := by
  let index : BitVec 32 := .ofNat 32 f.old.entry.index
  let next : BitVec 64 := .ofNat 64 f.old.next
  let previous : BitVec 64 := .ofNat 64 f.old.previous
  have newIndexSlot : DataSlot n o (f.base+28) 4 := .entry f.newOwner f.base 28 4 f.named (.inr (.inr rfl))
  have newNextSlot : LinkSlot n o (f.base+8) := .entry f.newOwner f.base 8 f.named (.inl rfl)
  have newBackSlot : LinkSlot n o (f.base+16) := .entry f.newOwner f.base 16 f.named (.inr rfl)
  have indexAddress : s.regs.rbp.toBitVec+28=BitVec.ofNat 64 (f.base+28) := by
    rw [newBase,BitVec.ofNat_add]; rfl
  have nextAddress : s.regs.rbp.toBitVec+8=BitVec.ofNat 64 (f.base+8) := by
    rw [newBase,BitVec.ofNat_add]; rfl
  have backAddress : s.regs.rbp.toBitVec+16=BitVec.ofNat 64 (f.base+16) := by
    rw [newBase,BitVec.ofNat_add]; rfl
  let first := write32 shadow (f.base+28) f.old.entry.index
  let second := write64 first (f.base+8) f.old.next
  let third := write64 second (f.base+16) f.old.previous
  have c1 : Core c initial ra true first result {s with dmem := copyIndex s index} := by
    have step := core.store facts _ 4 index.toInt (newIndexSlot.heap layout)
    simpa only [copyIndex,indexAddress,first,write32,index] using step
  have c2 : Core c initial ra true second result {s with dmem := copyNext s index next} := by
    have step := c1.store facts _ 8 next.toInt (newNextSlot.heap layout)
    simpa only [copyNext,nextAddress,second,write64,next] using step
  have c3 : Core c initial ra true third result {s with dmem := copyBack s index next previous} := by
    have step := c2.store facts _ 8 previous.toInt (newBackSlot.heap layout)
    simpa only [copyBack,backAddress,third,write64,previous] using step
  have c4 : Core c initial ra true (write64 third f.old.previous f.link) result
      {s with dmem := prefixMemory s index next previous} := by
    have step := c3.store facts _ 8 (BitVec.ofNat 64 f.link).toInt ((f.old.previousSlot layout).heap layout)
    have linkAddress : s.regs.rbp.toBitVec+8=BitVec.ofNat 64 f.link := by
      simpa only [ReplaceFocus.link,layout.hash] using nextAddress
    simpa only [prefixMemory,linkAddress,write64,previous] using step
  have oldIndexAddress : s.regs.rbx.toBitVec+28=BitVec.ofNat 64 (f.old.removed-o.hash+o.index) := by
    rw [oldBase,layout.index,BitVec.ofNat_add]; rfl
  have oldNextAddress : s.regs.rbx.toBitVec+8=BitVec.ofNat 64 (f.old.removed+o.next) := by
    rw [oldBase]
    change BitVec.ofNat 64 (f.old.removed-o.hash)+BitVec.ofNat 64 8=_
    rw [←BitVec.ofNat_add]
    congr 1
    have valid := f.old.fields.valid
    rw [layout.hash,layout.next] at *
    omega
  have oldBackAddress : s.regs.rbx.toBitVec+16=BitVec.ofNat 64 (f.old.removed+o.pprev) := by
    rw [oldBase]
    change BitVec.ofNat 64 (f.old.removed-o.hash)+BitVec.ofNat 64 16=_
    rw [←BitVec.ofNat_add]
    congr 1
    have valid := f.old.fields.valid
    rw [layout.hash,layout.pprev] at *
    omega
  have smallIndex := word_bound f.old.fields.index
  have smallNext := word_bound f.old.fields.forward
  have smallPrevious := word_bound f.old.fields.back
  have indexSlot : DataSlot n o (f.old.removed-o.hash+o.index) 4 := by
    rw [layout.index]
    exact .entry f.old.entry.owner (f.old.removed-o.hash) 28 4 f.old.fields.named (.inr (.inr rfl))
  have indexRead : s.dmem.loadInt (s.regs.rbx.toBitVec+28) 4=some (index.toNat : Int) := by
    rw [oldIndexAddress,core.load facts (indexSlot.heap layout)]
    simpa only [index,BitVec.toNat_ofNat,Nat.mod_eq_of_lt smallIndex] using word_loadInt _ _ _ _ _ f.old.fields.index
  have nextRead : (copyIndex s index).loadInt (s.regs.rbx.toBitVec+8) 8=some (next.toNat : Int) := by
    rw [oldNextAddress,c1.load facts ((f.old.fields.nextSlot layout).heap layout)]
    have read := word_after_index shadow f.old.entry.index layout storage f.named
      (f.old.fields.nextSlot layout) s!"bucket[{f.old.bucket}].next"
    rw [f.old.fields.forward] at read
    simpa only [first,next,BitVec.toNat_ofNat,Nat.mod_eq_of_lt smallNext] using word_loadInt _ _ _ _ _ read
  have backRead : (copyNext s index next).loadInt (s.regs.rbx.toBitVec+16) 8=some (previous.toNat : Int) := by
    rw [oldBackAddress,c2.load facts ((f.old.fields.backSlot layout).heap layout)]
    have apart := (f.old.fields.backSlot layout).disjoint newNextSlot layout storage (by
      have different := Ne.symm (f.next_ne_back layout storage f.old.fields)
      simpa only [ReplaceFocus.link,layout.hash,layout.next,Nat.add_zero] using different)
    have frame := word_write64_frame first "old.pprev" (f.old.removed+o.pprev) 8 (f.base+8) f.old.next apart
    have read := word_after_index shadow f.old.entry.index layout storage f.named (f.old.fields.backSlot layout) "old.pprev"
    have original := word_path f.old.fields.back "old.pprev"
    rw [original] at read
    rw [read] at frame
    simpa only [second,previous,BitVec.toNat_ofNat,Nat.mod_eq_of_lt smallPrevious] using word_loadInt _ _ _ _ _ frame
  have newIndex : (s.dmem.loadInt (s.regs.rbp.toBitVec+28) 4).isSome=true := by
    rw [indexAddress,core.load facts (newIndexSlot.heap layout)]
    exact mappedIndex
  have newNext : ((copyIndex s index).loadInt (s.regs.rbp.toBitVec+8) 8).isSome=true := by
    rw [nextAddress,c1.load facts (newNextSlot.heap layout)]
    exact storeInt_defined _ _ _ _ _ _ mappedNext
  have originalBack : (shadow.loadInt (.ofNat 64 (f.base+16)) 8).isSome=true := by
    have read := word_loadInt _ _ _ _ _ f.unlinked
    simp only [layout.hash,layout.pprev,Nat.add_assoc] at read
    rw [read]
    rfl
  have newBack : ((copyNext s index next).loadInt (s.regs.rbp.toBitVec+16) 8).isSome=true := by
    rw [backAddress,c2.load facts (newBackSlot.heap layout)]
    exact storeInt_defined _ _ _ _ _ _ (storeInt_defined _ _ _ _ _ _ originalBack)
  have predecessor : ((copyBack s index next previous).loadInt previous 8).isSome=true := by
    rw [c3.load facts ((f.old.previousSlot layout).heap layout)]
    apply storeInt_defined
    apply storeInt_defined
    apply storeInt_defined
    rw [word_loadInt _ _ _ _ _ (f.old.shape.predecessor_read f.old.member f.old.fields f.old.headRead)]
    rfl
  have region := region_eventually (IndexMutatorImage.Replace_r2b_layout.agreement agree) s _
    (splice_prefix s index next previous indexRead newIndex nextRead newNext backRead newBack predecessor)
  apply eventually_weaken (instructionStep fetch) _ _ _ _ region
  rintro t ⟨registers,memory,pc⟩
  have zero : next=0 ↔ f.old.next=0 := by
    constructor
    · intro h
      have v := congrArg BitVec.toNat h
      simpa [next,BitVec.toNat_ofNat,Nat.mod_eq_of_lt smallNext] using v
    · intro h; simp [next,h]
  have shadowEq : write64 third f.old.previous f.link=
      replacePrefixMemory shadow o f.link f.old.previous f.old.next f.old.entry.index := by
    simp only [replacePrefixMemory,ReplaceFocus.link,layout.hash,layout.next,layout.pprev,
      layout.index,Nat.add_sub_cancel,Nat.add_zero,Nat.add_assoc,first,second,third]
  rw [shadowEq] at c4
  refine ⟨by simpa only [zero] using pc,⟨?_,?_,?_,?_,?_,?_,?_,?_⟩,?_⟩
  · simpa only [registers] using core.stack
  · simpa only [registers] using core.owner
  · simpa only [registers] using core.new
  · simpa only [registers] using core.r13
  · simpa only [registers] using core.r14
  · simpa only [registers] using core.r15
  · simpa only [memory] using c4.memory
  · simpa only [memory] using c4.frame
  · simp only [registers,newBase,ReplaceFocus.link,layout.hash]
    apply UInt64.toBitVec_inj.mp
    change BitVec.ofNat 64 f.base+8=BitVec.ofNat 64 (f.base+8)
    rw [BitVec.ofNat_add]
    rfl

#print axioms splice
end Binary.Pair.Replace
