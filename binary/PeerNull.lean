import PeerFinish

namespace Binary.PeerGet
open TrustBase
local instance : Labels := Image.linkedLabels

/-- The null-pointer suffix takes the decoded null guard and clear-peer
    branch, then executes the common return suffix. It never reads a peer. -/
theorem null_suffix (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (contract : TracePcContract fetch)
    (initial : MachineState) (body : MachineData) (returnAddress : UInt64)
    (entry : EntryFrame initial returnAddress)
    (sp : body.regs.rsp = initial.data.regs.rsp - 48) (null : body.regs.rbx = 0)
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
      (fun final => Returned initial final returnAddress ∧ final.data.regs.rax = 0 ∧
        KcovState coverage preempt final.data.dmem ∧
        EqualOutside (fun address => InRange (body.regs.rsp.toBitVec-8) 8 address ∨
          KcovBufferBytes coverage address) body.dmem final.data.dmem)
      ⟨body, Image.PeerGet.entry + 0x12⟩ := by
  have guard := region_eventually (Image.PeerGet_r12_layout.agreement agree) body _ (null_guard body)
  apply eventually_trans (instructionStep fetch) _ _ _ guard
  rintro guarded ⟨guardRegs, guardMemory, guardPC⟩
  have atClear : guarded = ⟨guarded.data, Image.PeerGet.entry+0xdd⟩ := by
    cases guarded
    simp_all
  rw [atClear]
  have clear := region_eventually (Image.PeerGet_rdd_layout.agreement agree) guarded.data _
    (clear_peer guarded.data)
  apply eventually_trans (instructionStep fetch) _ _ _ clear
  rintro cleared ⟨clearRegs, clearMemory, clearPC⟩
  have regs : cleared.data.regs = body.regs := by
    rw [clearRegs, guardRegs, ← null]
  have memory : cleared.data.dmem = body.dmem := clearMemory.trans guardMemory
  have finish := finish_9d fetch agree contract initial cleared.data returnAddress entry
    (by simpa only [regs] using sp) coverage preempt (by simpa only [memory] using state)
    (by simpa only [regs] using aligned) (by simpa only [regs, memory] using mapped)
    (by simpa only [regs] using pushSeparate) (by simpa only [regs] using returnSeparate)
    metadataSeparate preemptSeparate writes (by simpa only [memory] using frame)
    (by simpa only [regs] using savedSeparate)
  have atFinish : cleared = ⟨cleared.data, Image.PeerGet.entry+0x9d⟩ := by
    cases cleared with
    | mk data pc => exact congrArg (fun pc => (⟨data, pc⟩ : MachineState)) clearPC
  rw [atFinish]
  apply eventually_weaken (instructionStep fetch) _ _ _ _ finish
  rintro final ⟨returned, result, state, frame⟩
  exact ⟨returned, by simpa only [regs, null] using result, state,
    by simpa only [regs, memory] using frame⟩

#print axioms null_suffix
end Binary.PeerGet
