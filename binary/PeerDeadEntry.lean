import WordAlignment
import PeerStart
import PeerLoad
import PeerDeadFinish

namespace Binary.PeerGet
open TrustBase
local instance : Labels := Image.linkedLabels

/-- Complete entry-to-return execution for a mapped nonnull peer with
    zero refcount. The physical field remains zero and the result is NULL.
    This is a physical helper theorem, not whole-World adequacy. -/
theorem dead_entry_to_return (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (contract : TracePcContract fetch) (traceCmp : TraceConstCmp4Contract fetch)
    (s : MachineData) (returnAddress : UInt64)
    (entry : EntryFrame ⟨s, Image.PeerGet.entry⟩ returnAddress) (nonnull : s.regs.rdi ≠ 0)
    (field : s.dmem.loadInt (s.regs.rdi.toBitVec+0x420) 4 = some 0)
    (coverage : KcovLayout) (preempt : BitVec 32)
    (state : KcovState coverage preempt s.dmem)
    (mapped : ∀ n < 7,
      (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true)
    (pushSeparate : ∀ address, KcovStateBytes coverage address →
      ¬InRange (s.regs.rsp.toBitVec - 56) 56 address)
    (coverageSeparate : KcovSeparated coverage (InRange (s.regs.rsp.toBitVec-56) 64))
    (metadataSeparate : KcovSeparated coverage (KcovMetadataBytes coverage))
    (preemptSeparate : KcovSeparated coverage (InRange preemptCountAddress 4))
    (fieldSeparate : ∀ a, InRange (s.regs.rdi.toBitVec+0x420) 4 a →
      ¬(InRange (s.regs.rsp.toBitVec-56) 56 a ∨ KcovBufferBytes coverage a)) :
    Eventually (instructionStep fetch)
      (fun final => Returned ⟨s, Image.PeerGet.entry⟩ final returnAddress ∧ final.data.regs.rax = 0 ∧
        KcovState coverage preempt final.data.dmem ∧
        EqualOutside (fun address => InRange (s.regs.rsp.toBitVec-56) 56 address ∨
          KcovBufferBytes coverage address) s.dmem final.data.dmem)
      ⟨s, Image.PeerGet.entry⟩ := by
  have headerSeparate : KcovSeparated coverage (InRange (s.regs.rsp.toBitVec-56) 8) := by
    intro address insideBuffer insideHeader
    obtain ⟨byte, bound, atByte⟩ := insideHeader
    exact coverageSeparate address insideBuffer ⟨byte, by omega, atByte⟩
  have start := prologue_and_return fetch agree contract s coverage preempt state entry.1 mapped
    pushSeparate headerSeparate metadataSeparate preemptSeparate
  apply eventually_trans (instructionStep fetch) _ _ _ start
  rintro body ⟨pc, rsp, rbx, state, prefixFrame⟩
  have bodyBase : body.data.regs.rsp.toBitVec = s.regs.rsp.toBitVec-48 := by simp [rsp]
  have callbackSlot : body.data.regs.rsp.toBitVec-8 = s.regs.rsp.toBitVec-56 := by
    rw [bodyBase, BitVec.sub_sub]
    rfl
  have savedBase : s.regs.rsp.toBitVec-48 = (s.regs.rsp.toBitVec-56)+8 := by
    rw [show (56 : BitVec 64) = 48+8 from rfl, ← BitVec.sub_sub, BitVec.sub_add_cancel]
  have bodyAligned : body.data.regs.rsp.toNat % 8 = 0 := by
    rw [rsp]
    exact aligned_sub _ 48 entry.1 (by decide)
  have bodyMapped : (body.data.dmem.loadInt (body.data.regs.rsp.toBitVec-8) 8).isSome = true := by
    rw [callbackSlot]
    have framed := prefixFrame.loadInt (s.regs.rsp.toBitVec-56) 8 (by
      intro byte bound written
      exact headerSeparate _ written ⟨byte, bound, rfl⟩)
    rw [← framed]
    have saved := saveMemory_read s 7 6 (by decide) (by decide)
    simpa [slot] using congrArg Option.isSome saved
  have bodyPush : ∀ address, KcovStateBytes coverage address →
      ¬InRange (body.data.regs.rsp.toBitVec-8) 8 address := by
    intro address kept inside
    rw [callbackSlot] at inside
    obtain ⟨byte, bound, atByte⟩ := inside
    exact pushSeparate address kept ⟨byte, by omega, atByte⟩
  have savedSeparate : ∀ address, InRange (s.regs.rsp.toBitVec-48) 56 address →
      ¬(KcovBufferBytes coverage address ∨ InRange (body.data.regs.rsp.toBitVec-8) 8 address ∨
        KcovBufferBytes coverage address) := by
    intro address inside written
    rw [savedBase] at inside
    have outside : ¬KcovBufferBytes coverage address := fun inBuffer =>
      coverageSeparate address inBuffer (stack_tail_inside _ _ inside)
    rcases written with h | h | h
    · exact outside h
    · rw [callbackSlot] at h
      exact stack_tail_disjoint_header _ _ inside h
    · exact outside h
  have ready : CallsReady coverage preempt body.data :=
    ⟨state, bodyAligned, bodyMapped, bodyPush,
      by simpa only [callbackSlot] using headerSeparate, metadataSeparate, preemptSeparate⟩
  have bodyField : body.data.dmem.loadInt (body.data.regs.rbx.toBitVec+0x420) 4 = some (0 : UInt32).toNat := by
    rw [rbx]
    have savedField := (saveMemory_frame s 7 (by decide)).loadInt (s.regs.rdi.toBitVec+0x420) 4 (by
      intro byte bound inside
      exact fieldSeparate _ ⟨byte, bound, rfl⟩ (.inl inside))
    have tracedField := prefixFrame.loadInt (s.regs.rdi.toBitVec+0x420) 4 (by
      intro byte bound inside
      exact fieldSeparate _ ⟨byte, bound, rfl⟩ (.inr inside))
    rw [← tracedField, ← savedField]
    exact field
  have load := load_prefix fetch agree contract traceCmp body.data
    (by simpa only [rbx] using nonnull) 0 bodyField coverage preempt ready (by
      intro a inside written
      rw [rbx] at inside
      apply fieldSeparate a inside
      rcases written with header | buffer
      · rw [callbackSlot] at header
        obtain ⟨byte, bound, atByte⟩ := header
        exact .inl ⟨byte, by omega, atByte⟩
      · exact .inr buffer)
  have atGuard : body = ⟨body.data, Image.PeerGet.entry+0x12⟩ := by
    cases body with
    | mk data _ => exact congrArg (fun pc => (⟨data, pc⟩ : MachineState)) pc
  rw [atGuard]
  apply eventually_trans (instructionStep fetch) _ _ _ load
  intro tested testPost
  have loadedReady : CallsReady coverage preempt (loaded body.data 0) :=
    ⟨ready.state, ready.aligned, ready.mapped, ready.pushSeparate, ready.returnSeparate,
      ready.metadataSeparate, ready.preemptSeparate⟩
  have testReady := testPost.next_ready loadedReady
  obtain ⟨testPC, testSP, _, testBP, _, _, _, _, _, testFrame, _⟩ := testPost
  have testSP' : tested.data.regs.rsp = body.data.regs.rsp := testSP
  have testZero : tested.data.regs.get (.low .rbp .W32) = 0 := by
    simp [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop, BitVec.take, testBP, loaded]
  have finish := zero_suffix fetch agree contract traceCmp ⟨s, Image.PeerGet.entry⟩
    tested.data returnAddress entry (testSP'.trans rsp) testZero coverage preempt testReady
    (fun a => KcovBufferBytes coverage a ∨ InRange (body.data.regs.rsp.toBitVec-8) 8 a ∨
      KcovBufferBytes coverage a)
    (prefixFrame.trans testFrame)
    (by
      intro a inside written
      rw [testSP'] at written
      apply savedSeparate a inside
      rcases written with (h | h | h) | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr h)
      · exact .inr (.inl h)
      · exact .inr (.inr h))
  have atTest : tested = ⟨tested.data, Image.PeerGet.entry+0x3b⟩ := by
    cases tested with
    | mk data _ => exact congrArg (fun pc => (⟨data, pc⟩ : MachineState)) testPC
  rw [atTest]
  apply eventually_weaken (instructionStep fetch) _ _ _ _ finish
  rintro final ⟨returned, result, state, suffixFrame⟩
  refine ⟨returned, result, state, ?_⟩
  intro address outside
  have outsideStack : ¬InRange (s.regs.rsp.toBitVec-56) 56 address := fun h => outside (.inl h)
  have outsideBuffer : ¬KcovBufferBytes coverage address := fun h => outside (.inr h)
  have outsideCall : ¬(InRange (body.data.regs.rsp.toBitVec-8) 8 address ∨
      KcovBufferBytes coverage address) := by
    rintro (header | buffer)
    · rw [callbackSlot] at header
      obtain ⟨byte, bound, atByte⟩ := header
      exact outsideStack ⟨byte, by omega, atByte⟩
    · exact outsideBuffer buffer
  have saved := saveMemory_frame s 7 (by decide) address outsideStack
  have prefixEq := prefixFrame address outsideBuffer
  have testedEq := testFrame address outsideCall
  have suffix := suffixFrame address (by simpa only [testSP'] using outsideCall)
  exact saved.trans (prefixEq.trans (testedEq.trans suffix))

#print axioms dead_entry_to_return
end Binary.PeerGet
