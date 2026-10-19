import PairRemoveFirstGuard

namespace Binary.Pair.Remove.First
open TrustBase CommonBitsCoverage Index Callback
local instance : Labels := Image.linkedLabels

theorem finish_body (fetch : Int64 → Option Decoded) (agree : IndexRemoveDecoderAgreement fetch)
    (bh : GuardedBh fetch) {n o c initial ra shadow s}
    (facts : CallFacts n o c initial ra 4) (core : Core c initial ra true shadow s) :
    Eventually (guardedStep fetch (StackGuard initial.data.regs.rsp)) (fun t => Returned initial t ra ∧
      MemoryReady c initial ra 4 (savedWords initial.data) false t.data.dmem ∧
      EqualOutside (External c initial 4) shadow t.data.dmem) ⟨s,codeEntry+0x4d⟩ := by
  have h0 : s.dmem.loadInt s.regs.rsp.toBitVec 8=some initial.data.regs.rbx.toNat := by
    rw [core.stack]
    exact core.memory.saved 2 (by decide)
  have h1 : s.dmem.loadInt (s.regs.rsp.toBitVec+8) 8=some initial.data.regs.rbp.toNat := by
    rw [core.stack,UInt64.toBitVec_sub]
    change s.dmem.loadInt ((initial.data.regs.rsp.toBitVec-24)+8) 8=_
    rw [show (24 : BitVec 64)=16+8 from rfl,←BitVec.sub_sub,BitVec.sub_add_cancel]
    exact core.memory.saved 1 (by decide)
  have h2 : s.dmem.loadInt (s.regs.rsp.toBitVec+16) 8=some initial.data.regs.r12.toNat := by
    rw [core.stack,UInt64.toBitVec_sub]
    change s.dmem.loadInt ((initial.data.regs.rsp.toBitVec-24)+16) 8=_
    rw [show (24 : BitVec 64)=8+16 from rfl,←BitVec.sub_sub,BitVec.sub_add_cancel]
    exact core.memory.saved 0 (by decide)
  have raw := tail_to_bh s initial.data.regs.rbx initial.data.regs.rbp initial.data.regs.r12 h0 h1 h2
  have region := region_guarded (outer := initial.data.regs.rsp) (IndexMutatorImage.Remove_r4d_layout.agreement agree) s _ (by rw [core.stack]; stack_path) raw
  apply eventually_trans (guardedStep fetch (StackGuard initial.data.regs.rsp)) _ _ _ region
  rintro entered ⟨registers,memory,entryPc⟩
  have sp : entered.data.regs.rsp=initial.data.regs.rsp := by
    simp only [registers,core.stack,UInt64.sub_add_cancel]
  have count : entered.data.dmem.loadInt preemptCountAddress 4=some (c.preempt+512).toNat := by
    rw [memory]
    exact load32_raw _ _ _ core.memory.preempt
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
      rw [memory]
      exact core.memory.pending gate
    · intro a written inside
      rw [sp] at inside
      have live := Stack.inside initial.data.regs.rsp.toBitVec 4 0 (by decide) a
        (by simpa [Stack.slot] using inside)
      exact facts.geometry.preemptLive a live written
  have entryFrame : EntryFrame entered ra := by
    refine ⟨by simpa only [sp] using facts.entry.1,?_⟩
    rw [sp,memory]
    exact core.memory.returnWord
  have service := bh initial.data.regs.rsp entered ra entryPc ready entryFrame (by rw [sp]; stack_not_return)
  apply eventually_weaken (guardedStep fetch (StackGuard initial.data.regs.rsp)) _ _ _ _ service
  rintro t ⟨returned,frame,effect⟩
  have restored : load32 t.data.dmem preemptCountAddress=some c.preempt := by
    have read := effect (c.preempt+512) count
    rw [arg] at read
    change t.data.dmem.loadInt preemptCountAddress 4=some ((c.preempt+512-512).toNat : Int) at read
    rw [BitVec.add_sub_cancel] at read
    simp only [load32,read,Option.map_some,BitVec.ofInt_natCast,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  have initialMem : MemoryReady c initial ra 4 (savedWords initial.data) true entered.data.dmem := by
    simpa only [memory] using core.memory
  refine ⟨⟨returned.1,?_,?_,?_,?_,?_,?_,?_⟩,
    initialMem.preempt_transition facts.geometry frame restored,?_⟩
  · simpa only [sp] using returned.2.1
  · simpa only [registers] using returned.2.2.1
  · simpa only [registers] using returned.2.2.2.1
  · simpa only [registers] using returned.2.2.2.2.1
  · simpa only [registers,core.r13] using returned.2.2.2.2.2.1
  · simpa only [registers,core.r14] using returned.2.2.2.2.2.2.1
  · simpa only [registers,core.r15] using returned.2.2.2.2.2.2.2
  · rw [memory] at frame
    apply external_trans core.frame
    intro a outside
    exact frame a (fun h => outside (.inr (.inr h)))

theorem finish (fetch : Int64 → Option Decoded) (agree : IndexRemoveDecoderAgreement fetch)
    (trace : GuardedPc fetch) (bh : GuardedBh fetch) {n o c initial ra shadow s}
    (facts : CallFacts n o c initial ra 4) (core : Core c initial ra true shadow s) :
    Eventually (guardedStep fetch (StackGuard initial.data.regs.rsp)) (fun t => Returned initial t ra ∧
      MemoryReady c initial ra 4 (savedWords initial.data) false t.data.dmem ∧
      EqualOutside (External c initial 4) shadow t.data.dmem) ⟨s,codeEntry+0x48⟩ := by
  have call := core_callback fetch (codeEntry+0x48) "L_ffffffff810f3100" trace
    (agree _ _ (by rfl)) facts core
  apply eventually_trans (guardedStep fetch (StackGuard initial.data.regs.rsp)) _ _ _ call
  rintro t ⟨pc,core,_,_⟩
  have atPc : t=⟨t.data,codeEntry+0x4d⟩ := by
    cases t
    simp_all
    rfl
  rw [atPc]
  exact finish_body fetch agree bh facts core

#print axioms finish_body
#print axioms finish
end Binary.Pair.Remove.First
