import PeerComparisons

namespace Binary.PeerGet
open TrustBase
local instance : Labels := Image.linkedLabels

/-- State after the actual successful increment and argument setup, with
    the caller stack pointer before the comparison CALL. -/
def incremented (s : MachineData) : MachineData :=
  {s with regs := {incrementRegisters s with rsp := s.regs.rsp}, dmem := incrementMemory s}

theorem increment_call (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (traceCmp : TraceConstCmp1Contract fetch)
    (s : MachineData) (coverage : KcovLayout) (preempt : BitVec 32)
    (ready : CallsReady coverage preempt s)
    (count : s.dmem.loadInt s.regs.r13.toBitVec 4 =
      some (s.regs.get (.low .rbp .W32)).toNat)
    (countSeparate : ∀ a, KcovStateBytes coverage a → ¬InRange s.regs.r13.toBitVec 4 a) :
    Eventually (instructionStep fetch) (CallPost (incremented s) coverage preempt 0x60)
      ⟨s, Image.PeerGet.entry+0x44⟩ := by
  have mapped := storeInt_defined s.dmem (s.regs.rsp.toBitVec-8) s.regs.r13.toBitVec 8 4
    (s.regs.get (.low .rbp .W32)+1).toInt ready.mapped
  obtain ⟨word, wordRead⟩ := Option.isSome_iff_exists.mp mapped
  have executed := region_eventually (Image.PeerGet_r44_layout.agreement agree) s _
    (increment s word count wordRead)
  apply eventually_trans (instructionStep fetch) _ _ _ executed
  rintro callee ⟨regs, memory, pc⟩
  have state : KcovState coverage preempt (incremented s).dmem :=
    Kcov.state_frame coverage preempt _ _ ready.state _
      (storeInt_frame s.dmem s.regs.r13.toBitVec 4 (s.regs.get (.low .rbp .W32)+1).toInt)
      countSeparate
  exact after_call fetch (.ofNat 0xffffffff810f3ec0) .constCmp1 traceCmp
    (incremented s) callee 0x60
    (by simpa only [incremented, incrementRegisters] using regs)
    memory pc coverage preempt state ready.aligned ready.pushSeparate ready.returnSeparate
    ready.metadataSeparate ready.preemptSeparate

theorem incremented_frame (s : MachineData) :
    EqualOutside (InRange s.regs.r13.toBitVec 4) s.dmem (incremented s).dmem :=
  storeInt_frame _ _ _ _

theorem incremented_count (s : MachineData) :
    (incremented s).dmem.loadInt s.regs.r13.toBitVec 4 =
      some ((s.regs.get (.low .rbp .W32)+1).toNat : Int) :=
  load32_store _ _ _

theorem incremented_ready (s : MachineData) (coverage : KcovLayout) (preempt : BitVec 32)
    (ready : CallsReady coverage preempt s)
    (countSeparate : ∀ a, KcovStateBytes coverage a → ¬InRange s.regs.r13.toBitVec 4 a) :
    CallsReady coverage preempt (incremented s) := by
  refine ⟨?_, ready.aligned, ?_, ready.pushSeparate, ready.returnSeparate,
    ready.metadataSeparate, ready.preemptSeparate⟩
  · exact Kcov.state_frame coverage preempt _ _ ready.state _ (incremented_frame s) countSeparate
  · exact storeInt_defined _ _ _ _ _ _ ready.mapped

theorem incremented_registers (s : MachineData) :
    (incremented s).regs.rsp = s.regs.rsp ∧
    (incremented s).regs.rbx = s.regs.rbx ∧
    (incremented s).regs.rbp = s.regs.rbp ∧
    (incremented s).regs.r13 = s.regs.r13 ∧
    (incremented s).regs.get (.low .r12 .W32) = s.regs.get (.low .rbp .W32)+1 ∧
    (incremented s).regs.get (.low .r15 .W8) = 1 := by
  simp [incremented, incrementRegisters, Reg64s.get, Reg64s.get64, Reg64s.set,
    Reg64s.set64, Reg.base, Reg.offset, BitVec.drop, BitVec.take, BitVec.replaceLow]

  rw [BitVec.extractLsb'_setWidth_of_le (by decide), BitVec.extractLsb'_append_eq_right]
  simp

#print axioms increment_call
#print axioms incremented_count
#print axioms incremented_registers
#print axioms incremented_ready
end Binary.PeerGet
