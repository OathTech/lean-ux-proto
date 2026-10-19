import PairReplaceFirstEnable

namespace Binary.Pair.Replace.First
open TrustBase CommonBitsCoverage Index Callback
local instance : Labels := Image.linkedLabels

theorem restore (fetch : Int64 → Option Decoded) (agree : IndexReplaceDecoderAgreement fetch)
    {c initial ra shadow result s} (core : Core c initial ra false shadow result s) :
    Eventually (guardedStep fetch (StackGuard initial.data.regs.rsp)) (fun t => Returned initial t ra ∧
      MemoryReady c initial ra 5 (savedWords initial.data) false t.data.dmem ∧
      EqualOutside (External c initial 5) shadow t.data.dmem ∧
      t.data.regs.rax.toBitVec.setWidth 8=result.toBitVec.setWidth 8) ⟨s,codeEntry+0x97⟩ := by
  have slot (i : Nat) (bound : i≤4) :
      s.regs.rsp.toBitVec+BitVec.ofNat 64 (8*i)=Stack.slot initial.data.regs.rsp.toBitVec (4-i) := by
    rw [core.stack,UInt64.toBitVec_sub]
    change Stack.slot initial.data.regs.rsp.toBitVec 4+BitVec.ofNat 64 (8*i)=_
    rw [Stack.window _ 4 (4-i) (by omega)]
    have equal : 4-(4-i)=i := by omega
    rw [equal]
  have h0 : s.dmem.loadInt s.regs.rsp.toBitVec 8=some (initial.data.regs.rbx.toNat : Int) := by
    have address := slot 0 (by decide)
    change s.regs.rsp.toBitVec+0#64=Stack.slot initial.data.regs.rsp.toBitVec 4 at address
    rw [BitVec.add_zero] at address
    rw [address]
    exact core.memory.saved 3 (by decide)
  have h1 : s.dmem.loadInt (s.regs.rsp.toBitVec+8) 8=some (initial.data.regs.rbp.toNat : Int) := by
    have address := slot 1 (by decide)
    change s.regs.rsp.toBitVec+8=Stack.slot initial.data.regs.rsp.toBitVec 3 at address
    rw [address]
    exact core.memory.saved 2 (by decide)
  have h2 : s.dmem.loadInt (s.regs.rsp.toBitVec+16) 8=some (initial.data.regs.r12.toNat : Int) := by
    have address := slot 2 (by decide)
    change s.regs.rsp.toBitVec+16=Stack.slot initial.data.regs.rsp.toBitVec 2 at address
    rw [address]
    exact core.memory.saved 1 (by decide)
  have h3 : s.dmem.loadInt (s.regs.rsp.toBitVec+24) 8=some (initial.data.regs.r13.toNat : Int) := by
    have address := slot 3 (by decide)
    change s.regs.rsp.toBitVec+24=Stack.slot initial.data.regs.rsp.toBitVec 1 at address
    rw [address]
    exact core.memory.saved 0 (by decide)
  have h4 : s.dmem.loadInt (s.regs.rsp.toBitVec+32) 8=some (ra.toNat : Int) := by
    have address := slot 4 (by decide)
    change s.regs.rsp.toBitVec+32=Stack.slot initial.data.regs.rsp.toBitVec 0 at address
    rw [address]
    change s.dmem.loadInt (initial.data.regs.rsp.toBitVec-0#64) 8=some (ra.toNat : Int)
    rw [BitVec.sub_zero]
    exact core.memory.returnWord
  have region := region_guarded (outer := initial.data.regs.rsp) (IndexMutatorImage.Replace_r97_layout.agreement agree) s _ (by rw [core.stack]; stack_path)
    (restore_return s initial.data.regs.rbx initial.data.regs.rbp initial.data.regs.r12 initial.data.regs.r13 ra h0 h1 h2 h3 h4)
  apply eventually_weaken (guardedStep fetch (StackGuard initial.data.regs.rsp)) _ _ _ _ region
  rintro t ⟨registers,memory,pc⟩
  refine ⟨⟨pc,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,?_⟩
  · rw [registers,core.stack]
    apply UInt64.toBitVec_inj.mp
    change (initial.data.regs.rsp.toBitVec-32)+40=initial.data.regs.rsp.toBitVec+8
    rw [show (40 : BitVec 64)=32+8 from rfl,←BitVec.add_assoc,BitVec.sub_add_cancel]
  · simp only [registers]
  · simp only [registers]
  · simp only [registers]
  · simp only [registers]
  · simpa only [registers] using core.r14
  · simpa only [registers] using core.r15
  · simpa only [memory] using core.memory
  · simpa only [memory] using core.frame
  · simp only [registers,returnWord,UInt64.toBitVec_ofBitVec,core.r13]
    rw [BitVec.setWidth_setWidth_of_le _ (by decide : 8≤64),
      BitVec.setWidth_setWidth_of_le _ (by decide : 8≤32)]

theorem finish (fetch : Int64 → Option Decoded) (agree : IndexReplaceDecoderAgreement fetch)
    (trace : GuardedPc fetch) (bh : GuardedBh fetch)
    {n o c initial ra shadow result s} (facts : CallFacts n o c initial ra 5)
    (core : Core c initial ra true shadow result s) :
    Eventually (guardedStep fetch (StackGuard initial.data.regs.rsp)) (fun t => Returned initial t ra ∧
      MemoryReady c initial ra 5 (savedWords initial.data) false t.data.dmem ∧
      EqualOutside (External c initial 5) shadow t.data.dmem ∧
      t.data.regs.rax.toBitVec.setWidth 8=result.toBitVec.setWidth 8) ⟨s,codeEntry+0x81⟩ := by
  have callback := core_callback fetch (codeEntry+0x81) "L_ffffffff810f3100" trace (agree _ _ (by rfl)) facts core
  apply eventually_trans (guardedStep fetch (StackGuard initial.data.regs.rsp)) _ _ _ callback
  rintro called ⟨pc,core,_,_⟩
  apply eventually_trans (guardedStep fetch (StackGuard initial.data.regs.rsp)) _ _ _ (Callback.at_pc pc (enable fetch agree bh facts core))
  rintro enabled ⟨pc,core⟩
  exact Callback.at_pc pc (restore fetch agree core)

#print axioms restore
#print axioms finish
end Binary.Pair.Replace.First
