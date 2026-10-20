import PeerDeadCallbacks
import PeerFinish

namespace Binary.PeerGet
open TrustBase
local instance : Labels := Image.linkedLabels

/-- Complete the zero-refcount branch, including all six instrumentation
    calls, clearing the result register, and the real epilogue. Zero remains
    an admitted physical count; this lemma makes no liveness assumption. -/
theorem dead_finish (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch)
    (tracePc : TracePcContract fetch) (traceCmp : TraceConstCmp4Contract fetch)
    (initial : MachineState) (body : MachineData) (returnAddress : UInt64)
    (entry : EntryFrame initial returnAddress)
    (sp : body.regs.rsp = initial.data.regs.rsp - 48)
    (coverage : KcovLayout) (preempt : BitVec 32)
    (ready : CallsReady coverage preempt body)
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
      ⟨body, Image.PeerGet.entry + 0xb0⟩ := by
  have callbacks := dead_callbacks fetch agree tracePc traceCmp body coverage preempt ready
  apply eventually_trans (instructionStep fetch) _ _ _ callbacks
  intro afterCallbacks post
  have ready' := post.next_ready ready
  obtain ⟨pc, rsp, _, _, _, _, _, _, _, callbackFrame, _⟩ := post
  have atClear : afterCallbacks = ⟨afterCallbacks.data, Image.PeerGet.entry+0xdd⟩ := by
    cases afterCallbacks with
    | mk data _ => exact congrArg (fun pc => (⟨data, pc⟩ : MachineState)) pc
  rw [atClear]
  have clear := region_eventually (Image.PeerGet_rdd_layout.agreement agree)
    afterCallbacks.data _ (clear_peer afterCallbacks.data)
  apply eventually_trans (instructionStep fetch) _ _ _ clear
  rintro cleared ⟨regs, memory, pc⟩
  have clearSP : cleared.data.regs.rsp = body.regs.rsp := by simpa only [regs] using rsp
  have finish := finish_9d fetch agree tracePc initial cleared.data returnAddress entry
    (clearSP.trans sp) coverage preempt
    (by simpa only [memory] using ready'.state)
    (by simpa only [regs] using ready'.aligned)
    (by simpa only [regs, memory] using ready'.mapped)
    (by simpa only [regs] using ready'.pushSeparate)
    (by simpa only [regs] using ready'.returnSeparate)
    ready'.metadataSeparate ready'.preemptSeparate
    (fun a => writes a ∨ InRange (body.regs.rsp.toBitVec-8) 8 a ∨ KcovBufferBytes coverage a)
    (by rw [memory]; exact frame.trans callbackFrame)
    (by
      intro a inside written
      rw [clearSP] at written
      apply savedSeparate a inside
      rcases written with (h | h | h) | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr h)
      · exact .inr (.inl h)
      · exact .inr (.inr h))
  have atFinish : cleared = ⟨cleared.data, Image.PeerGet.entry+0x9d⟩ := by
    cases cleared with
    | mk data _ => exact congrArg (fun pc => (⟨data, pc⟩ : MachineState)) pc
  rw [atFinish]
  apply eventually_weaken (instructionStep fetch) _ _ _ _ finish
  rintro final ⟨returned, result, state, suffixFrame⟩
  refine ⟨returned, by simpa only [regs] using result, state, ?_⟩
  rw [memory, clearSP] at suffixFrame
  intro address outside
  exact (callbackFrame address outside).trans (suffixFrame address outside)

theorem zero_suffix (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch)
    (tracePc : TracePcContract fetch) (traceCmp : TraceConstCmp4Contract fetch)
    (initial : MachineState) (body : MachineData) (returnAddress : UInt64)
    (entry : EntryFrame initial returnAddress)
    (sp : body.regs.rsp = initial.data.regs.rsp - 48)
    (zero : body.regs.get (.low .rbp .W32) = 0)
    (coverage : KcovLayout) (preempt : BitVec 32)
    (ready : CallsReady coverage preempt body)
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
      ⟨body, Image.PeerGet.entry + 0x3b⟩ := by
  have guard := region_eventually (Image.PeerGet_r3b_layout.agreement agree) body _ (zero_guard body)
  apply eventually_trans (instructionStep fetch) _ _ _ guard
  rintro guarded ⟨regs, memory, pc⟩
  have atDead : guarded = ⟨guarded.data, Image.PeerGet.entry+0xb0⟩ := by
    have pc' : guarded.pc = Image.PeerGet.entry+0xb0 := by simpa only [zero, ite_true] using pc
    cases guarded with
    | mk data _ => exact congrArg (fun pc => (⟨data, pc⟩ : MachineState)) pc'
  rw [atDead]
  have ready' : CallsReady coverage preempt guarded.data :=
    ⟨by simpa only [memory] using ready.state,
      by simpa only [regs] using ready.aligned,
      by simpa only [regs, memory] using ready.mapped,
      by simpa only [regs] using ready.pushSeparate,
      by simpa only [regs] using ready.returnSeparate,
      ready.metadataSeparate, ready.preemptSeparate⟩
  have finish := dead_finish fetch agree tracePc traceCmp initial guarded.data returnAddress entry
    (by simpa only [regs] using sp) coverage preempt ready' writes
    (by simpa only [memory] using frame) (by simpa only [regs] using savedSeparate)
  apply eventually_weaken (instructionStep fetch) _ _ _ _ finish
  intro final post
  simpa only [regs, memory] using post

#print axioms zero_suffix

#print axioms dead_finish
end Binary.PeerGet
