import PeerIncrement
import PeerLiveFinish

namespace Binary.PeerGet
open TrustBase
local instance : Labels := Image.linkedLabels

/-- Successful CMPXCHG through the real return. The accepted bound concerns
    the loaded count; no refcount restriction is imposed on the dead branch. -/
theorem increment_and_finish (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch)
    (tracePc : TracePcContract fetch) (traceCmp : TraceConstCmp4Contract fetch)
    (traceByte : TraceConstCmp1Contract fetch)
    (initial : MachineState) (body : MachineData) (returnAddress : UInt64)
    (entry : EntryFrame initial returnAddress)
    (sp : body.regs.rsp = initial.data.regs.rsp - 48)
    (coverage : KcovLayout) (preempt : BitVec 32)
    (ready : CallsReady coverage preempt body)
    (count : body.dmem.loadInt body.regs.r13.toBitVec 4 =
      some (body.regs.get (.low .rbp .W32)).toNat)
    (bound : (body.regs.get (.low .rbp .W32)).toNat+1 < 2^31)
    (countSeparate : ∀ a, KcovStateBytes coverage a → ¬InRange body.regs.r13.toBitVec 4 a)
    (fieldSeparate : ∀ a, InRange body.regs.r13.toBitVec 4 a →
      ¬(InRange (body.regs.rsp.toBitVec-8) 8 a ∨ KcovBufferBytes coverage a))
    (writes : BitVec 64 → Prop)
    (frame : EqualOutside writes (saveMemory initial.data 7) body.dmem)
    (savedSeparate : ∀ a, InRange (initial.data.regs.rsp.toBitVec-48) 56 a →
      ¬(writes a ∨ InRange body.regs.r13.toBitVec 4 a ∨
        InRange (body.regs.rsp.toBitVec-8) 8 a ∨ KcovBufferBytes coverage a)) :
    Eventually (instructionStep fetch)
      (fun final => Returned initial final returnAddress ∧ final.data.regs.rax = body.regs.rbx ∧
        KcovState coverage preempt final.data.dmem ∧
        final.data.dmem.loadInt body.regs.r13.toBitVec 4 =
          some ((body.regs.get (.low .rbp .W32)+1).toNat : Int) ∧
        EqualOutside (fun a => InRange body.regs.r13.toBitVec 4 a ∨
          InRange (body.regs.rsp.toBitVec-8) 8 a ∨ KcovBufferBytes coverage a)
          body.dmem final.data.dmem)
      ⟨body, Image.PeerGet.entry+0x44⟩ := by
  have call := increment_call fetch agree traceByte body coverage preempt ready count countSeparate
  apply eventually_trans (instructionStep fetch) _ _ _ call
  intro tested post
  have ready' := post.next_ready (incremented_ready body coverage preempt ready countSeparate)
  obtain ⟨pc, rsp, rbx, rbp, r12, _, _, r15, _, callbackFrame, _⟩ := post
  obtain ⟨_, incBX, incBP, _, incR12, incR15⟩ := incremented_registers body
  have testSP : tested.data.regs.rsp = body.regs.rsp := rsp
  have testBP : tested.data.regs.get (.low .rbp .W32) = body.regs.get (.low .rbp .W32) := by
    simp only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, rbp, incBP]
  have testR12 : tested.data.regs.get (.low .r12 .W32) = body.regs.get (.low .rbp .W32)+1 := by
    simpa only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, r12] using incR12
  have testR15 : tested.data.regs.get (.low .r15 .W8) = 1 := by
    simpa only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, r15] using incR15
  have signs := count_signs (body.regs.get (.low .rbp .W32)).toNat bound
  simp only [BitVec.ofNat_toNat] at signs
  have finish := live_finish fetch agree tracePc traceCmp initial tested.data returnAddress entry
    (testSP.trans sp) coverage preempt ready'
    (by rw [testR15]; decide) (by rw [testBP]; exact signs.1) (by rw [testR12]; exact signs.2)
    (fun a => (writes a ∨ InRange body.regs.r13.toBitVec 4 a) ∨
      InRange (body.regs.rsp.toBitVec-8) 8 a ∨ KcovBufferBytes coverage a)
    ((frame.trans (incremented_frame body)).trans callbackFrame)
    (by
      intro a inside written
      rw [testSP] at written
      apply savedSeparate a inside
      rcases written with ((h | h) | h | h) | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr h))
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr h)))
  have atFinish : tested = ⟨tested.data, Image.PeerGet.entry+0x60⟩ := by
    cases tested with
    | mk data _ => exact congrArg (fun pc => (⟨data, pc⟩ : MachineState)) pc
  rw [atFinish]
  apply eventually_weaken (instructionStep fetch) _ _ _ _ finish
  rintro final ⟨returned, result, state, suffixFrame⟩
  rw [testSP] at suffixFrame
  have afterIncrement : EqualOutside (fun a => InRange (body.regs.rsp.toBitVec-8) 8 a ∨
      KcovBufferBytes coverage a) (incremented body).dmem final.data.dmem := by
    intro a outside
    exact (callbackFrame a outside).trans (suffixFrame a outside)
  refine ⟨returned, result.trans (rbx.trans incBX), state, ?_, ?_⟩
  · rw [← afterIncrement.loadInt body.regs.r13.toBitVec 4 (by
      intro byte bound; exact fieldSeparate _ ⟨byte, bound, rfl⟩)]
    exact incremented_count body
  · exact (incremented_frame body).trans afterIncrement

theorem live_suffix (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch)
    (tracePc : TracePcContract fetch) (traceCmp : TraceConstCmp4Contract fetch)
    (traceByte : TraceConstCmp1Contract fetch)
    (initial : MachineState) (body : MachineData) (returnAddress : UInt64)
    (entry : EntryFrame initial returnAddress)
    (sp : body.regs.rsp = initial.data.regs.rsp - 48)
    (coverage : KcovLayout) (preempt : BitVec 32)
    (ready : CallsReady coverage preempt body)
    (count : body.dmem.loadInt body.regs.r13.toBitVec 4 =
      some (body.regs.get (.low .rbp .W32)).toNat)
    (nonzero : body.regs.get (.low .rbp .W32) ≠ 0)
    (bound : (body.regs.get (.low .rbp .W32)).toNat+1 < 2^31)
    (countSeparate : ∀ a, KcovStateBytes coverage a → ¬InRange body.regs.r13.toBitVec 4 a)
    (fieldSeparate : ∀ a, InRange body.regs.r13.toBitVec 4 a →
      ¬(InRange (body.regs.rsp.toBitVec-8) 8 a ∨ KcovBufferBytes coverage a))
    (writes : BitVec 64 → Prop)
    (frame : EqualOutside writes (saveMemory initial.data 7) body.dmem)
    (savedSeparate : ∀ a, InRange (initial.data.regs.rsp.toBitVec-48) 56 a →
      ¬(writes a ∨ InRange body.regs.r13.toBitVec 4 a ∨
        InRange (body.regs.rsp.toBitVec-8) 8 a ∨ KcovBufferBytes coverage a)) :
    Eventually (instructionStep fetch)
      (fun final => Returned initial final returnAddress ∧ final.data.regs.rax = body.regs.rbx ∧
        KcovState coverage preempt final.data.dmem ∧
        final.data.dmem.loadInt body.regs.r13.toBitVec 4 =
          some ((body.regs.get (.low .rbp .W32)+1).toNat : Int) ∧
        EqualOutside (fun a => InRange body.regs.r13.toBitVec 4 a ∨
          InRange (body.regs.rsp.toBitVec-8) 8 a ∨ KcovBufferBytes coverage a)
          body.dmem final.data.dmem)
      ⟨body, Image.PeerGet.entry+0x3b⟩ := by
  have branchRun := zero_guard body
  simp only [ite_eq_right nonzero] at branchRun
  have call := guard_pc_region fetch Image.PeerGet.r3b 0x3b 0x3f
    (Image.PeerGet_r3b_layout.agreement agree) (Image.PeerGet_r3f_layout.agreement agree)
    tracePc body (by simpa using branchRun) coverage preempt ready
  apply eventually_trans (instructionStep fetch) _ _ _ call
  intro tested post
  have ready' := post.next_ready ready
  obtain ⟨pc, rsp, rbx, rbp, _, r13, _, _, _, callbackFrame, _⟩ := post
  have testCount : tested.data.regs.get (.low .rbp .W32) = body.regs.get (.low .rbp .W32) := by
    simp only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, rbp]
  have count' : tested.data.dmem.loadInt tested.data.regs.r13.toBitVec 4 =
      some (tested.data.regs.get (.low .rbp .W32)).toNat := by
    rw [r13, testCount, ← callbackFrame.loadInt body.regs.r13.toBitVec 4 (by
      intro byte bound; exact fieldSeparate _ ⟨byte, bound, rfl⟩)]
    exact count
  have finish := increment_and_finish fetch agree tracePc traceCmp traceByte initial tested.data
    returnAddress entry (rsp.trans sp) coverage preempt ready' count'
    (by simpa only [testCount] using bound)
    (by simpa only [r13] using countSeparate)
    (by simpa only [r13, rsp] using fieldSeparate)
    (fun a => writes a ∨ InRange (body.regs.rsp.toBitVec-8) 8 a ∨ KcovBufferBytes coverage a)
    (frame.trans callbackFrame)
    (by
      intro a inside written
      rw [rsp, r13] at written
      apply savedSeparate a inside
      rcases written with (h | h | h) | h | h | h
      · exact .inl h
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr h))
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr h)))
  have atFinish : tested = ⟨tested.data, Image.PeerGet.entry+0x44⟩ := by
    cases tested with
    | mk data _ => exact congrArg (fun pc => (⟨data, pc⟩ : MachineState)) pc
  rw [atFinish]
  apply eventually_weaken (instructionStep fetch) _ _ _ _ finish
  rintro final ⟨returned, result, state, countFinal, suffixFrame⟩
  rw [rsp, r13] at suffixFrame
  refine ⟨returned, result.trans rbx, state, ?_, ?_⟩
  · simpa only [r13, testCount] using countFinal
  · intro a outside
    exact (callbackFrame a (fun h => outside (.inr h))).trans (suffixFrame a outside)

#print axioms live_suffix

#print axioms increment_and_finish
end Binary.PeerGet
