import PeerCall
import PeerReturn

namespace Binary.PeerGet
open TrustBase
local instance : Labels := Image.linkedLabels

/-- The shared suffix of all three peer-get paths: final coverage call,
    six register restores and the real return to the entry frame. -/
theorem finish_9d (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (contract : TracePcContract fetch)
    (initial : MachineState) (body : MachineData) (returnAddress : UInt64)
    (entry : EntryFrame initial returnAddress)
    (sp : body.regs.rsp = initial.data.regs.rsp - 48)
    (coverage : KcovLayout) (preempt : BitVec 32)
    (state : KcovState coverage preempt body.dmem)
    (aligned : body.regs.rsp.toNat % 8 = 0)
    (mapped : (body.dmem.loadInt (body.regs.rsp.toBitVec - 8) 8).isSome = true)
    (pushSeparate : ∀ address, KcovStateBytes coverage address →
      ¬InRange (body.regs.rsp.toBitVec - 8) 8 address)
    (returnSeparate : KcovSeparated coverage (InRange (body.regs.rsp.toBitVec - 8) 8))
    (metadataSeparate : KcovSeparated coverage (KcovMetadataBytes coverage))
    (preemptSeparate : KcovSeparated coverage (InRange preemptCountAddress 4))
    (writes : BitVec 64 → Prop)
    (frame : EqualOutside writes (saveMemory initial.data 7) body.dmem)
    (savedSeparate : ∀ address, InRange (initial.data.regs.rsp.toBitVec-48) 56 address →
      ¬(writes address ∨ InRange (body.regs.rsp.toBitVec-8) 8 address ∨
        KcovBufferBytes coverage address)) :
    Eventually (instructionStep fetch)
      (fun final => Returned initial final returnAddress ∧ final.data.regs.rax = body.regs.rbx ∧
        KcovState coverage preempt final.data.dmem ∧
        EqualOutside (fun address => InRange (body.regs.rsp.toBitVec-8) 8 address ∨
          KcovBufferBytes coverage address) body.dmem final.data.dmem)
      ⟨body, Image.PeerGet.entry + 0x9d⟩ := by
  have layout : LaidOut fetch (Image.PeerGet.entry + .ofNat 0x9d) Image.PeerGet.r1b :=
    Image.PeerGet_r9d_layout.agreement agree
  have traced := trace_and_return fetch 0x9d layout contract body coverage preempt state
    aligned mapped pushSeparate returnSeparate metadataSeparate preemptSeparate
  apply eventually_trans (instructionStep fetch) _ _ _ traced
  rintro afterTrace ⟨pc, rsp, rbx, _, _, _, _, _, state, traceFrame⟩
  have finish := return_from_saved fetch agree initial afterTrace.data returnAddress entry
    (rsp.trans sp) _ (frame.trans traceFrame) savedSeparate
  have sameStart : afterTrace = ⟨afterTrace.data, Image.PeerGet.entry + 0xa2⟩ := by
    cases afterTrace
    simp_all
  rw [sameStart]
  apply eventually_weaken (instructionStep fetch) _ _ _ _ finish
  rintro final ⟨returned, result, memory⟩
  exact ⟨returned, result.trans rbx, memory ▸ state, memory ▸ traceFrame⟩

#print axioms finish_9d
end Binary.PeerGet
