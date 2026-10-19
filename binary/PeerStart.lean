import WordAlignment
import KcovExecution
import ImageLayout

set_option maxHeartbeats 1000000

namespace Binary.PeerGet
open TrustBase
local instance : Labels := Image.linkedLabels

/-- Execute the helper's actual prologue and first coverage call. The
    resulting frame is relative to the six saved registers and callback
    return word actually pushed by those instructions. -/
theorem prologue_and_return (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (contract : TracePcContract fetch)
    (s : MachineData) (coverage : KcovLayout) (preempt : BitVec 32)
    (state : KcovState coverage preempt s.dmem)
    (aligned : s.regs.rsp.toNat % 8 = 0)
    (mapped : ∀ n < 7,
      (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true)
    (pushSeparate : ∀ address, KcovStateBytes coverage address →
      ¬InRange (s.regs.rsp.toBitVec - 56) 56 address)
    (returnSeparate : KcovSeparated coverage (InRange (s.regs.rsp.toBitVec-56) 8))
    (metadataSeparate : KcovSeparated coverage (KcovMetadataBytes coverage))
    (preemptSeparate : KcovSeparated coverage (InRange preemptCountAddress 4)) :
    Eventually (instructionStep fetch)
      (fun t => t.pc = Image.PeerGet.entry + 0x12 ∧
        t.data.regs.rsp = s.regs.rsp - 48 ∧ t.data.regs.rbx = s.regs.rdi ∧
        KcovState coverage preempt t.data.dmem ∧
        EqualOutside (KcovBufferBytes coverage) (saveMemory s 7) t.data.dmem)
      ⟨s, Image.PeerGet.entry⟩ := by
  have layout := Image.PeerGet_r00_layout.agreement agree
  have start := region_eventually layout s _ (prologue s mapped)
  apply eventually_trans (instructionStep fetch) _ _ _ start
  rintro callee ⟨regs, memory, pc⟩
  have calleeSP : callee.data.regs.rsp.toBitVec = s.regs.rsp.toBitVec-56 := by simp [regs]
  have calleeState : KcovState coverage preempt callee.data.dmem := by
    rw [memory]
    exact Kcov.state_frame coverage preempt _ _ state _
      (saveMemory_frame s 7 (by decide)) pushSeparate
  have entry : EntryFrame callee (Image.PeerGet.entry+0x12).toUInt64 := by
    constructor
    · simp only [regs]
      change (s.regs.rsp - 56).toNat % 8 = 0
      exact aligned_sub _ 56 aligned (by decide)
    · rw [calleeSP, memory]
      have saved := saveMemory_read s 7 6 (by decide) (by decide)
      simpa [slot, savedWords] using saved
  have returned := Kcov.callback_endpoint fetch (.ofNat 0xffffffff810f31f0) .pc contract
    coverage preempt callee (Image.PeerGet.entry+0x12).toUInt64 pc entry calleeState
    (by simpa only [calleeSP] using returnSeparate) metadataSeparate preemptSeparate
  apply eventually_weaken (instructionStep fetch) _ _ _ _ returned
  rintro t ⟨ret, state, frame⟩
  refine ⟨?_, ?_, ?_, state, ?_⟩
  · simpa using ret.1
  · rw [ret.2.1, regs]
    apply UInt64.toBitVec_inj.mp
    change (s.regs.rsp.toBitVec-56)+8 = s.regs.rsp.toBitVec-48
    rw [show (56 : BitVec 64) = 48+8 from rfl, ← BitVec.sub_sub, BitVec.sub_add_cancel]
  · simpa only [regs] using ret.2.2.1
  · simpa only [memory] using frame

#print axioms prologue_and_return
end Binary.PeerGet
