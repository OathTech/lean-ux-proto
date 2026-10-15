import PeerStart
import PeerLoad
import PeerIncrementFinish

namespace Binary.PeerGet
open TrustBase
local instance : Labels := Image.linkedLabels

/-- Entry-to-return physical execution of the accepted nonzero-count path.
    The loaded count is incremented once and the original peer is returned. -/
theorem live_entry_to_return (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (contract : TracePcContract fetch) (traceCmp : TraceConstCmp4Contract fetch)
    (traceByte : TraceConstCmp1Contract fetch)
    (s : MachineData) (returnAddress : UInt64)
    (entry : EntryFrame ⟨s, Image.PeerGet.entry⟩ returnAddress) (nonnull : s.regs.rdi ≠ 0)
    (count : UInt32) (nonzero : count ≠ 0) (bound : count.toNat+1 < 2^31)
    (field : s.dmem.loadInt (s.regs.rdi.toBitVec+0x420) 4 = some count.toNat)
    (coverage : KcovLayout) (preempt : BitVec 32)
    (state : KcovState coverage preempt s.dmem)
    (mapped : ∀ n < 7,
      (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true)
    (pushSeparate : ∀ address, KcovStateBytes coverage address →
      ¬InRange (s.regs.rsp.toBitVec - 56) 56 address)
    (coverageSeparate : KcovSeparated coverage (InRange (s.regs.rsp.toBitVec-56) 64))
    (metadataSeparate : KcovSeparated coverage (KcovMetadataBytes coverage))
    (preemptSeparate : KcovSeparated coverage (InRange preemptCountAddress 4))
    (countSeparate : ∀ a, KcovStateBytes coverage a → ¬InRange (s.regs.rdi.toBitVec+0x420) 4 a)
    (fieldSeparate : ∀ a, InRange (s.regs.rdi.toBitVec+0x420) 4 a →
      ¬(InRange (s.regs.rsp.toBitVec-56) 64 a ∨ KcovBufferBytes coverage a)) :
    Eventually (instructionStep fetch)
      (fun final => Returned ⟨s, Image.PeerGet.entry⟩ final returnAddress ∧ final.data.regs.rax = s.regs.rdi ∧
        KcovState coverage preempt final.data.dmem ∧
        final.data.dmem.loadInt (s.regs.rdi.toBitVec+0x420) 4 = some ((count.toBitVec+1).toNat : Int) ∧
        EqualOutside (fun address => InRange (s.regs.rdi.toBitVec+0x420) 4 address ∨ InRange (s.regs.rsp.toBitVec-56) 56 address ∨
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
    simp only [UInt64.toNat_sub, show (48 : UInt64).toNat = 48 from rfl]
    have aligned := entry.1
    change s.regs.rsp.toNat % 8 = 0 at aligned
    omega
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
  have bodyField : body.data.dmem.loadInt (body.data.regs.rbx.toBitVec+0x420) 4 = some count.toNat := by
    rw [rbx]
    have savedField := (saveMemory_frame s 7 (by decide)).loadInt (s.regs.rdi.toBitVec+0x420) 4 (by
      intro byte bound inside
      obtain ⟨i, hi, eq⟩ := inside
      exact fieldSeparate _ ⟨byte, bound, rfl⟩ (.inl ⟨i, by omega, eq⟩))
    have tracedField := prefixFrame.loadInt (s.regs.rdi.toBitVec+0x420) 4 (by
      intro byte bound inside
      exact fieldSeparate _ ⟨byte, bound, rfl⟩ (.inr inside))
    rw [← tracedField, ← savedField]
    exact field
  have load := load_prefix fetch agree contract traceCmp body.data
    (by simpa only [rbx] using nonnull) count bodyField coverage preempt ready (by
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
  have loadedReady : CallsReady coverage preempt (loaded body.data count) :=
    ⟨ready.state, ready.aligned, ready.mapped, ready.pushSeparate, ready.returnSeparate,
      ready.metadataSeparate, ready.preemptSeparate⟩
  have testReady := testPost.next_ready loadedReady
  obtain ⟨testPC, testSP, testBX, testBP, _, testR13, _, _, _, testFrame, _⟩ := testPost
  have testSP' : tested.data.regs.rsp = body.data.regs.rsp := testSP
  have testCount : tested.data.regs.get (.low .rbp .W32) = count.toBitVec := by
    simp [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop, BitVec.take, testBP, loaded]
    rw [BitVec.extractLsb'_setWidth_of_le (by decide)]
    simp
  have testFieldAddr : tested.data.regs.r13.toBitVec = s.regs.rdi.toBitVec+0x420 := by
    simp [testR13, loaded, rbx]
  have count' : tested.data.dmem.loadInt tested.data.regs.r13.toBitVec 4 =
      some (tested.data.regs.get (.low .rbp .W32)).toNat := by
    rw [testFieldAddr, testCount]
    have testField := testFrame.loadInt (s.regs.rdi.toBitVec+0x420) 4 (by
      intro byte hb written
      apply fieldSeparate _ ⟨byte, hb, rfl⟩
      rcases written with h | h
      · change InRange (body.data.regs.rsp.toBitVec-8) 8 _ at h
        rw [callbackSlot] at h
        obtain ⟨i, hi, eq⟩ := h
        exact .inl ⟨i, by omega, eq⟩
      · exact .inr h)
    rw [← testField]
    simpa only [loaded, rbx, UInt32.toNat_toBitVec] using bodyField
  have finish := live_suffix fetch agree contract traceCmp traceByte ⟨s, Image.PeerGet.entry⟩
    tested.data returnAddress entry (testSP'.trans rsp) coverage preempt testReady count'
    (by rw [testCount]; exact fun h => nonzero (UInt32.toBitVec_inj.mp h))
    (by simpa only [testCount, UInt32.toNat_toBitVec] using bound)
    (by simpa only [testFieldAddr] using countSeparate)
    (by
      intro a inside written
      rw [testFieldAddr] at inside
      apply fieldSeparate a inside
      rcases written with h | h
      · rw [testSP', callbackSlot] at h
        obtain ⟨i, hi, eq⟩ := h
        exact .inl ⟨i, by omega, eq⟩
      · exact .inr h)
    (fun a => KcovBufferBytes coverage a ∨ InRange (body.data.regs.rsp.toBitVec-8) 8 a ∨
      KcovBufferBytes coverage a)
    (prefixFrame.trans testFrame)
    (by
      intro a inside written
      rw [testSP', testFieldAddr] at written
      rcases written with (h | h | h) | h | h | h
      · exact savedSeparate a inside (.inl h)
      · exact savedSeparate a inside (.inr (.inl h))
      · exact savedSeparate a inside (.inr (.inr h))
      · apply fieldSeparate a h
        rw [savedBase] at inside
        exact .inl (stack_tail_inside _ _ inside)
      · exact savedSeparate a inside (.inr (.inl h))
      · exact savedSeparate a inside (.inr (.inr h)))
  have atTest : tested = ⟨tested.data, Image.PeerGet.entry+0x3b⟩ := by
    cases tested with
    | mk data _ => exact congrArg (fun pc => (⟨data, pc⟩ : MachineState)) testPC
  rw [atTest]
  apply eventually_weaken (instructionStep fetch) _ _ _ _ finish
  rintro final ⟨returned, result, state, finalCount, suffixFrame⟩
  refine ⟨returned, result.trans (testBX.trans rbx), state, ?_, ?_⟩
  · simpa only [testFieldAddr, testCount] using finalCount
  intro address outside
  have outsideField : ¬InRange (s.regs.rdi.toBitVec+0x420) 4 address := fun h => outside (.inl h)
  have outsideStack : ¬InRange (s.regs.rsp.toBitVec-56) 56 address := fun h => outside (.inr (.inl h))
  have outsideBuffer : ¬KcovBufferBytes coverage address := fun h => outside (.inr (.inr h))
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
  have suffix := suffixFrame address (by
    rw [testSP', testFieldAddr]
    rintro (h | h)
    · exact outsideField h
    · exact outsideCall h)
  exact saved.trans (prefixEq.trans (testedEq.trans suffix))

#print axioms live_entry_to_return
end Binary.PeerGet
