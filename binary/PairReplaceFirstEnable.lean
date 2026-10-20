import PairReplaceFirstGuard
import PairReplaceTailRegions
import PairCallSlot

namespace Binary.Pair.Replace.First
open TrustBase CommonBitsCoverage Index Callback
local instance : Labels := Image.linkedLabels

theorem enable (fetch : Int64 → Option Decoded) (agree : IndexReplaceDecoderAgreement fetch)
    (bh : GuardedBh fetch) {n o c initial ra shadow result s}
    (facts : CallFacts n o c initial ra 5) (core : Core c initial ra true shadow result s) :
    Eventually (guardedStep fetch (StackGuard initial.data.regs.rsp)) (fun t => t.pc=codeEntry+0x97 ∧
      Core c initial ra false shadow result t.data) ⟨s,codeEntry+0x86⟩ := by
  have mapped := core.memory.mapped 4 (by decide)
  change (s.dmem.loadInt (Stack.slot initial.data.regs.rsp.toBitVec 5) 8).isSome=true at mapped
  rw [←core.call_slot] at mapped
  obtain ⟨old,read⟩ := Option.isSome_iff_exists.mp mapped
  have run := region_guarded (outer := initial.data.regs.rsp) (IndexMutatorImage.Replace_r86_layout.agreement agree) s _ (by rw [core.stack]; stack_path) (call_bh s old read)
  apply eventually_trans (guardedStep fetch (StackGuard initial.data.regs.rsp)) _ _ _ run
  rintro entered ⟨registers,memory,entryPc⟩
  have sp : entered.data.regs.rsp.toBitVec=Stack.slot initial.data.regs.rsp.toBitVec 5 := by
    rw [registers]
    exact core.call_slot
  have mem : MemoryReady c initial ra 5 (savedWords initial.data) true entered.data.dmem := by
    rw [memory,core.call_slot]
    exact core.memory.call_store facts (by decide) (by decide) _
  have count : entered.data.dmem.loadInt preemptCountAddress 4=some (c.preempt+512).toNat :=
    load32_raw _ _ _ mem.preempt
  have arg : entered.data.regs.get (.low .rsi .W32)=512#32 := by
    simp [registers,Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.drop,BitVec.take]
  have ready : BhEnableReady entered := by
    refine ⟨c.preempt+512,count,facts.hardirq,?_,?_⟩
    · intro gate
      rw [arg] at gate
      change (c.preempt+512+1-512) &&& 0x00ffff00=0 at gate
      have arithmetic : c.preempt+512+1-512=c.preempt+1 := by
        rw [BitVec.add_assoc,BitVec.add_comm (512 : BitVec 32) 1,←BitVec.add_assoc,BitVec.add_sub_cancel]
      rw [arithmetic] at gate
      exact mem.pending gate
    · intro a written inside
      rw [sp] at inside
      exact facts.geometry.preemptLive a (Stack.inside _ 5 5 (by decide) a inside) written
  have entryFrame : EntryFrame entered (codeEntry+0x97).toUInt64 := by
    refine ⟨?_,?_⟩
    · rw [registers,core.stack]
      change (initial.data.regs.rsp-32-8).toNat%8=0
      have arithmetic : initial.data.regs.rsp-32-8=initial.data.regs.rsp-40 := by
        apply UInt64.toBitVec_inj.mp
        change (initial.data.regs.rsp.toBitVec-32)-8=initial.data.regs.rsp.toBitVec-40
        rw [BitVec.sub_sub]
        rfl
      rw [arithmetic]
      exact aligned_sub _ 40 facts.entry.1 (by decide)
    · rw [sp,memory,core.call_slot,load64_store]
      rfl
  have service := bh initial.data.regs.rsp entered (codeEntry+0x97).toUInt64 entryPc ready entryFrame (by rw [registers,core.stack]; stack_not_return)
  apply eventually_weaken (guardedStep fetch (StackGuard initial.data.regs.rsp)) _ _ _ _ service
  rintro t ⟨returned,frame,effect⟩
  have restored : load32 t.data.dmem preemptCountAddress=some c.preempt := by
    have read := effect (c.preempt+512) count
    rw [arg] at read
    change t.data.dmem.loadInt preemptCountAddress 4=some ((c.preempt+512-512).toNat : Int) at read
    rw [BitVec.add_sub_cancel] at read
    simp only [load32,read,Option.map_some,BitVec.ofInt_natCast,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  refine ⟨?_,⟨?_,?_,?_,?_,?_,?_,mem.preempt_transition facts.geometry frame restored,?_⟩⟩
  · exact returned.1
  · rw [returned.2.1,registers,UInt64.sub_add_cancel]
    exact core.stack
  · rw [returned.2.2.1,registers]; exact core.owner
  · rw [returned.2.2.2.1,registers]; exact core.new
  · rw [returned.2.2.2.2.2.1,registers]; exact core.r13
  · rw [returned.2.2.2.2.2.2.1,registers]; exact core.r14
  · rw [returned.2.2.2.2.2.2.2,registers]; exact core.r15
  · have callFrame := storeInt_frame s.dmem (s.regs.rsp.toBitVec-8) 8 (codeEntry+0x97).toBitVec.toInt
    apply external_trans core.frame
    intro a outside
    have first := callFrame a (by
      rw [core.call_slot]
      intro inside
      exact outside (.inl (Stack.scratch _ 5 5 (by decide) (by decide) a inside)))
    rw [←memory] at first
    exact first.trans (frame a (fun inside => outside (.inr (.inr inside))))

#print axioms enable
end Binary.Pair.Replace.First
