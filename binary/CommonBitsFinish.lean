import CommonBitsBodySteps

namespace Binary.CommonBits
open TrustBase
local instance : Labels := Image.linkedLabels

structure ReturnPost (i : Input) (c : CommonBitsCoverage.Context) (before : MachineData)
    (answer : Nat) (after : MachineState) : Prop where
  pc : after.pc = .ofBitVec i.returnAddress.toBitVec
  stack : after.data.regs.rsp = i.stack+40
  rbx : after.data.regs.rbx = i.savedBx
  rbp : after.data.regs.rbp = i.savedBp
  r12 : after.data.regs.r12 = i.savedR12
  r13 : after.data.regs.r13 = i.savedR13
  r14 : after.data.regs.r14 = before.regs.r14
  r15 : after.data.regs.r15 = before.regs.r15
  result : (after.data.regs.get (.low .rax .W8)).toNat = answer
  coverage : c.At after.data.dmem
  frame : EqualOutside (i.Writes c) before.dmem after.data.dmem
  callbackMapped : (after.data.dmem.loadInt (i.stack.toBitVec-8) 8).isSome = true

theorem ReturnPost.before {i c s t u answer} (final : ReturnPost i c t answer u)
    (r14 : t.regs.r14 = s.regs.r14) (r15 : t.regs.r15 = s.regs.r15)
    (frame : EqualOutside (i.Writes c) s.dmem t.dmem) : ReturnPost i c s answer u := by
  exact {final with
    r14 := final.r14.trans r14, r15 := final.r15.trans r15,
    frame := fun a outside => (frame a outside).trans (final.frame a outside)}

/-- Compose a proved region/callback step with a proved continuation, retaining
    the same physical frame and ABI registers back to the original state. -/
theorem chain_step (fetch : Int64 → Option Decoded)
    (i : Input) (c : CommonBitsCoverage.Context) (s : MachineData) (initial : MachineState)
    (pc : Int64) (bx bp : UInt64) (answer : Nat)
    (run : Eventually (instructionStep fetch) (BodyStep i c s pc bx bp) initial)
    (next : ∀ t : MachineData, BodyAt i c t → t.regs.rbx = bx → t.regs.rbp = bp →
      Eventually (instructionStep fetch) (ReturnPost i c t answer) ⟨t, pc⟩) :
    Eventually (instructionStep fetch) (ReturnPost i c s answer) initial := by
  apply eventually_trans (instructionStep fetch) _ _ _ run
  intro t step
  have cont := next t.data step.body step.rbx step.rbp
  have pcEq : (⟨t.data, pc⟩ : MachineState) = t := by cases t; congr 1; exact step.atPC.symm
  rw [pcEq] at cont
  apply eventually_weaken (instructionStep fetch) _ _ _ _ cont
  intro final post
  exact post.before step.r14 step.r15 step.frame


private theorem byte32 (v : BitVec 32) :
    (v.setWidth 64).extractLsb' 0 8 = v.setWidth 8 := by
  rw [BitVec.extractLsb'_setWidth_of_le (by decide)]
  rw [← BitVec.setWidth_eq_extractLsb' (by decide)]

private theorem low_byte (v : BitVec 64) :
    (v.extractLsb' 0 32).setWidth 8 = v.extractLsb' 0 8 := by
  apply BitVec.eq_of_toNat_eq
  simp

/-- Execute the complete six-instruction epilogue and the actual RET load. -/
theorem simple_return (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (offset : Nat)
    (layout : LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry+.ofNat offset)
      AllowedipsImage.CommonBits.r43)
    (i : Input) (c : CommonBitsCoverage.Context) (s : MachineData) (state : BodyAt i c s) :
    Eventually (instructionStep fetch)
      (ReturnPost i c s (s.regs.get (.low .rbp .W8)).toNat)
      ⟨s, AllowedipsImage.CommonBits.entry+.ofNat offset⟩ := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := state.stack_words
  have run := region_eventually (layout.agreement agree) s _
    (epilogue offset s i.savedBx i.savedBp i.savedR12 i.savedR13 i.returnAddress h0 h1 h2 h3 h4)
  apply eventually_weaken (instructionStep fetch) _ _ _ _ run
  rintro t ⟨regs, memory, pc⟩
  refine ⟨pc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [regs, state.stack]
  · simp only [regs]
  · simp only [regs]
  · simp only [regs]
  · simp only [regs]
  · simp only [regs]
  · simp only [regs]
  · simp [regs, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
      BitVec.take, BitVec.drop, byte32, low_byte]
  · simpa only [memory] using state.ready.state
  · intro a outside
    simp only [memory]
  · simpa only [memory,state.stack] using state.ready.mapped

/-- The IPv6 epilogue subtracts EBX before restoring the four saved registers. -/
theorem ipv6_return (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch)
    (i : Input) (c : CommonBitsCoverage.Context) (s : MachineData) (state : BodyAt i c s) :
    Eventually (instructionStep fetch)
      (ReturnPost i c s (((s.regs.get (.low .rbp .W32)) -
        (s.regs.get (.low .rbx .W32))).setWidth 8).toNat)
      ⟨s, AllowedipsImage.CommonBits.entry+0xb9⟩ := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := state.stack_words
  have run := ipv6_epilogue_execution fetch agree s i.savedBx i.savedBp i.savedR12 i.savedR13
    i.returnAddress h0 h1 h2 h3 h4
  apply eventually_weaken (instructionStep fetch) _ _ _ _ run
  rintro t ⟨regs, memory, pc⟩
  refine ⟨pc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [regs, state.stack]
  · simp only [regs]
  · simp only [regs]
  · simp only [regs]
  · simp only [regs]
  · simp only [regs]
  · simp only [regs]
  · simp [regs, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
      BitVec.take, BitVec.drop, byte32]
  · simpa only [memory] using state.ready.state
  · intro a outside
    simp only [memory]
  · simpa only [memory,state.stack] using state.ready.mapped

end Binary.CommonBits
