import WordAlignment
import KcovExecution
import ImageLayout

set_option maxHeartbeats 1000000

namespace Binary.PeerGet
open TrustBase
local instance : Labels := Image.linkedLabels

/-- A trace CALL followed by its service return, with physical callback
    state preserved. The write footprint includes the actual pushed word. -/
theorem trace_and_return (fetch : Int64 → Option Decoded)
    (offset : Nat) (layout : LaidOut fetch (Image.PeerGet.entry + .ofNat offset) Image.PeerGet.r1b)
    (contract : TracePcContract fetch) (s : MachineData)
    (coverage : KcovLayout) (preempt : BitVec 32)
    (state : KcovState coverage preempt s.dmem)
    (aligned : s.regs.rsp.toNat % 8 = 0)
    (mapped : (s.dmem.loadInt (s.regs.rsp.toBitVec - 8) 8).isSome = true)
    (pushSeparate : ∀ address, KcovStateBytes coverage address →
      ¬InRange (s.regs.rsp.toBitVec - 8) 8 address)
    (returnSeparate : KcovSeparated coverage (InRange (s.regs.rsp.toBitVec - 8) 8))
    (metadataSeparate : KcovSeparated coverage (KcovMetadataBytes coverage))
    (preemptSeparate : KcovSeparated coverage (InRange preemptCountAddress 4)) :
    Eventually (instructionStep fetch)
      (fun t => t.pc = Image.PeerGet.entry + .ofNat (offset+5) ∧
        t.data.regs.rsp = s.regs.rsp ∧
        t.data.regs.rbx = s.regs.rbx ∧ t.data.regs.rbp = s.regs.rbp ∧
        t.data.regs.r12 = s.regs.r12 ∧ t.data.regs.r13 = s.regs.r13 ∧
        t.data.regs.r14 = s.regs.r14 ∧ t.data.regs.r15 = s.regs.r15 ∧
        KcovState coverage preempt t.data.dmem ∧
        EqualOutside (fun address => InRange (s.regs.rsp.toBitVec - 8) 8 address ∨
          KcovBufferBytes coverage address) s.dmem t.data.dmem)
      ⟨s, Image.PeerGet.entry + .ofNat offset⟩ := by
  obtain ⟨word, wordRead⟩ := Option.isSome_iff_exists.mp mapped
  have call := region_eventually layout s _ (trace_call offset s word wordRead)
  apply eventually_trans (instructionStep fetch) _ _ _ call
  rintro callee ⟨regs, memory, pc⟩
  have pushed := storeInt_frame s.dmem (s.regs.rsp.toBitVec - 8) 8
    (Image.PeerGet.entry + .ofNat (offset+5)).toBitVec.toInt
  have calleeState : KcovState coverage preempt callee.data.dmem := by
    rw [memory]
    exact Kcov.state_frame coverage preempt _ _ state _ pushed pushSeparate
  have calleeSP : callee.data.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 8 := by simp [regs]
  have entry : EntryFrame callee (Image.PeerGet.entry + .ofNat (offset+5)).toUInt64 := by
    constructor
    · simp only [regs]
      change (s.regs.rsp - 8).toNat % 8 = 0
      exact aligned_sub _ 8 aligned (by decide)
    · rw [calleeSP, memory]
      change (callMemory s (offset+5)).loadInt (s.regs.rsp.toBitVec-8) 8 = _
      have stored := load64_store s.dmem (s.regs.rsp.toBitVec-8)
        (Image.PeerGet.entry + .ofNat (offset+5)).toBitVec
      exact stored
  have returned := Kcov.callback_endpoint fetch (.ofNat 0xffffffff810f3100) .pc contract
    coverage preempt callee (Image.PeerGet.entry + .ofNat (offset+5)).toUInt64 pc entry calleeState
    (by simpa only [calleeSP] using returnSeparate) metadataSeparate preemptSeparate
  apply eventually_weaken (instructionStep fetch) _ _ _ _ returned
  rintro t ⟨ret, state, frame⟩
  obtain ⟨returnPC, rsp, rbx, rbp, r12, r13, r14, r15⟩ := ret
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, state, ?_⟩
  · simpa using returnPC
  · rw [rsp, regs]
    apply UInt64.toBitVec_inj.mp
    change (s.regs.rsp.toBitVec - 8) + 8 = s.regs.rsp.toBitVec
    exact BitVec.sub_add_cancel _ _
  · simpa only [regs] using rbx
  · simpa only [regs] using rbp
  · simpa only [regs] using r12
  · simpa only [regs] using r13
  · simpa only [regs] using r14
  · simpa only [regs] using r15
  · rw [memory] at frame
    exact pushed.trans frame

#print axioms trace_and_return
end Binary.PeerGet
