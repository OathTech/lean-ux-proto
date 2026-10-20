import PeerLiveCallbacks
import PeerFinish

namespace Binary.PeerGet
open TrustBase
local instance : Labels := Image.linkedLabels

/-- Execute the successful helper's instrumented tests and real epilogue. -/
theorem live_finish (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch)
    (tracePc : TracePcContract fetch) (traceCmp : TraceConstCmp4Contract fetch)
    (initial : MachineState) (body : MachineData) (returnAddress : UInt64)
    (entry : EntryFrame initial returnAddress)
    (sp : body.regs.rsp = initial.data.regs.rsp - 48)
    (coverage : KcovLayout) (preempt : BitVec 32)
    (ready : CallsReady coverage preempt body)
    (success : body.regs.get (.low .r15 .W8) ≠ 0)
    (oldPositive : (body.regs.get (.low .rbp .W32)).msb = false)
    (newPositive : (body.regs.get (.low .r12 .W32)).msb = false)
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
      ⟨body, Image.PeerGet.entry + 0x60⟩ := by
  have callbacks := live_callbacks fetch agree tracePc traceCmp body coverage preempt ready
    success oldPositive newPositive
  apply eventually_trans (instructionStep fetch) _ _ _ callbacks
  intro tested post
  have ready' := post.next_ready ready
  obtain ⟨pc, rsp, rbx, _, _, _, _, _, _, callbackFrame, _⟩ := post
  have finish := finish_9d fetch agree tracePc initial tested.data returnAddress entry
    (rsp.trans sp) coverage preempt ready'.state ready'.aligned ready'.mapped
    ready'.pushSeparate ready'.returnSeparate ready'.metadataSeparate ready'.preemptSeparate
    (fun a => writes a ∨ InRange (body.regs.rsp.toBitVec-8) 8 a ∨ KcovBufferBytes coverage a)
    (frame.trans callbackFrame)
    (by
      intro a inside written
      rw [rsp] at written
      apply savedSeparate a inside
      rcases written with (h | h | h) | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr h)
      · exact .inr (.inl h)
      · exact .inr (.inr h))
  have atFinish : tested = ⟨tested.data, Image.PeerGet.entry+0x9d⟩ := by
    cases tested with
    | mk data _ => exact congrArg (fun pc => (⟨data, pc⟩ : MachineState)) pc
  rw [atFinish]
  apply eventually_weaken (instructionStep fetch) _ _ _ _ finish
  rintro final ⟨returned, result, state, suffixFrame⟩
  refine ⟨returned, result.trans rbx, state, ?_⟩
  rw [rsp] at suffixFrame
  intro address outside
  exact (callbackFrame address outside).trans (suffixFrame address outside)

#print axioms live_finish
end Binary.PeerGet
