import PairInsertAddress

namespace Binary.Pair.Insert
open TrustBase CommonBitsCoverage Index
local instance : Labels := Image.linkedLabels

/-- Enter the locked recheck with the same reconstructed chain. The only
memory write is the second preempt-count increment. -/
theorem nested_entry (fetch : Int64 → Option Decoded) (decoder : IndexInsertDecoderAgreement fetch)
    {n o c initial ra shadow s} (facts : FrameFacts n o c initial ra)
    (core : Core n o c initial ra .outer shadow s) (layout : Layout o)
    (focus : InsertFocus n o shadow)
    (table : initial.data.regs.rdi.toNat=n.table) (owner : initial.data.regs.rsi.toNat=focus.fresh.base) :
    Eventually (instructionStep fetch) (fun t => t.pc=walkStart true focus.nodes ∧
      Core n o c initial ra .inner shadow t.data ∧ WalkRegisters true focus.index t.data ∧
      t.data.regs.rbx.toBitVec=BitVec.ofNat 64 (Index.head focus.nodes)) ⟨s,codeEntry+0xd1⟩ := by
  have nested := core.nested_memory facts
  have disable := region_eventually (nested_disable_layout.agreement decoder) s _
    (nested_disable_region s (c.preempt+512) (load32_raw _ _ _ core.memory.preempt))
  apply eventually_trans (instructionStep fetch) _ _ _ disable
  rintro disabled ⟨disabledRegs,disabledHeap,pc⟩
  have core : Core n o c initial ra .inner shadow disabled.data := nested.same disabledRegs disabledHeap
  have small : focus.index<2^32 := word_bound focus.indexRead
  have indexAddress : disabled.data.regs.rbp.toBitVec+28=BitVec.ofNat 64 (focus.fresh.base+o.index) := by
    rw [core.owner_address owner,layout.index,BitVec.ofNat_add]
    rfl
  have indexRead : disabled.data.dmem.loadInt (disabled.data.regs.rbp.toBitVec+28) 4=
      some (BitVec.ofNat 32 focus.index).toNat := by
    rw [indexAddress,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
    have slot : DataSlot n o (focus.fresh.base+o.index) 4 := by
      rw [layout.index]
      exact .entry focus.fresh.owner focus.fresh.base 28 4 focus.fresh.named (.inr (.inr rfl))
    rw [←core.frame.loadInt _ _ (slot.heap layout)]
    exact word_loadInt _ _ _ _ _ focus.indexRead
  have loadIndex := region_eventually (nested_index_layout.agreement decoder) disabled.data _
    (nested_index_region disabled.data (.ofNat 32 focus.index) indexRead)
  apply eventually_trans (instructionStep fetch) _ _ _ (at_pc pc loadIndex)
  rintro indexed ⟨indexedRegs,indexedHeap,pc⟩
  have core : Core n o c initial ra .inner shadow indexed.data :=
    ⟨by rw [indexedRegs]; exact core.stack,by rw [indexedRegs]; exact core.table,
      by rw [indexedRegs]; exact core.owner,indexedHeap ▸ core.memory,indexedHeap ▸ core.frame⟩
  have mask := region_eventually (nested_mask_layout.agreement decoder) indexed.data _
    (nested_mask_region indexed.data (.ofNat 32 focus.index) (by rw [indexedRegs]))
  apply eventually_trans (instructionStep fetch) _ _ _ (at_pc pc mask)
  rintro masked ⟨maskedRegs,maskedHeap,pc⟩
  have core : Core n o c initial ra .inner shadow masked.data :=
    ⟨by rw [maskedRegs]; exact core.stack,by rw [maskedRegs]; exact core.table,
      by rw [maskedRegs]; exact core.owner,maskedHeap ▸ core.memory,maskedHeap ▸ core.frame⟩
  have headBound : Index.head focus.nodes<2^64 := word_bound focus.headRead
  have headValue : (UInt64.ofNat (Index.head focus.nodes)).toNat=Index.head focus.nodes := by
    change Index.head focus.nodes%2^64=Index.head focus.nodes
    exact Nat.mod_eq_of_lt headBound
  have address : masked.data.regs.r12.toBitVec+masked.data.regs.r14.toBitVec*8=
      nestedBucketAddress masked.data (.ofNat 32 focus.index) := by rw [nestedBucketAddress,maskedRegs]
  have headRead : masked.data.dmem.loadInt
      (masked.data.regs.r12.toBitVec+masked.data.regs.r14.toBitVec*8) 8=
      some (UInt64.ofNat (Index.head focus.nodes)).toNat := by
    rw [address,core.bucket_address layout table,headValue]
    rw [←core.frame.loadInt _ _ ((LinkSlot.table _ (Nat.mod_lt _ (by decide))).heap layout)]
    exact word_loadInt _ _ _ _ _ focus.headRead
  have physical := nested_head_region masked.data (.ofNat (Index.head focus.nodes)) headRead
  have run := region_eventually (nested_head_layout.agreement decoder) masked.data _ physical
  apply eventually_trans (instructionStep fetch) _ _ _ (at_pc pc run)
  rintro loaded ⟨loadedRegs,loadedHeap,pc⟩
  have test := region_eventually (nested_test_layout.agreement decoder) loaded.data _ (nested_test_region loaded.data)
  apply eventually_weaken (instructionStep fetch) _ _ _ _ (at_pc pc test)
  rintro t ⟨regs,heap,pc⟩
  have regs := regs.trans loadedRegs
  have heap := heap.trans loadedHeap
  refine ⟨?_,⟨by rw [regs]; exact core.stack,by rw [regs]; exact core.table,
    by rw [regs]; exact core.owner,heap ▸ core.memory,heap ▸ core.frame⟩,?_,?_⟩
  · rw [loadedRegs] at pc
    exact pc
  · constructor
    · rw [regs,maskedRegs,indexedRegs]
      change (focus.index%2^32)%2^64=focus.index
      rw [Nat.mod_eq_of_lt small,Nat.mod_eq_of_lt (by omega : focus.index<2^64)]
    · intro _
      rw [regs,maskedRegs]
      exact mask_index focus.index
  · rw [regs]
    rfl

#print axioms nested_entry
end Binary.Pair.Insert
