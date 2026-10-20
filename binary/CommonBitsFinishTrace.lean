import CommonBitsRestoreTrace
import CommonBitsTracedSteps

namespace Binary.CommonBits
open TrustBase
local instance : Labels := Image.linkedLabels

private theorem low8 (v : BitVec 32) : (v.setWidth 64).extractLsb' 0 8 = v.setWidth 8 := by
  rw [BitVec.extractLsb'_setWidth_of_le (by decide)]
  rw [← BitVec.setWidth_eq_extractLsb' (by decide)]

private theorem low_byte (v : BitVec 64) :
    (v.extractLsb' 0 32).setWidth 8 = v.extractLsb' 0 8 := by
  apply BitVec.eq_of_toNat_eq
  simp

/-- The RET is executed after the proved restore prefix, not abstracted by an ABI premise. -/
theorem finish_from_restore (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch)
    (i : Input) (c : CommonBitsCoverage.Context) (s : MachineData) (state : BodyAt i c s)
    (start : Int64) (retOffset : Nat) (retMember : retOffset ∈ [0x4b,0x74,0xc3])
    (word : BitVec 32) (rxSection : Nat)
    (returnTarget : Int64.ofBitVec i.returnAddress.toBitVec = AllowedipsImage.Lookup.entry+0xea)
    (prefixRun : Eventually (historyStep fetch) (fun t =>
      (t.machine.data.regs = {s.regs with
        rax := .ofBitVec (word.setWidth 64),
        rbx := i.savedBx, rbp := i.savedBp, r12 := i.savedR12, r13 := i.savedR13,
        rsp := s.regs.rsp+32} ∧ t.machine.data.dmem = s.dmem ∧
        t.machine.pc = AllowedipsImage.CommonBits.entry+.ofNat retOffset) ∧
      Local (i.Writes c) ⟨s,start⟩ rxSection [] t) ⟨⟨s,start⟩,[⟨s,start⟩]⟩) :
    Eventually (historyStep fetch) (fun t => ReturnPost i c s (word.setWidth 8).toNat t.machine ∧
      Local (i.Writes c) ⟨s,start⟩ rxSection [returnedView] t) ⟨⟨s,start⟩,[⟨s,start⟩]⟩ := by
  apply chain fetch (i.Writes c) ⟨s,start⟩ rxSection [] [returnedView]
    (fun t => t.data.regs = {s.regs with
      rax := .ofBitVec (word.setWidth 64), rbx := i.savedBx, rbp := i.savedBp,
      r12 := i.savedR12, r13 := i.savedR13, rsp := s.regs.rsp+32} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.CommonBits.entry+.ofNat retOffset)
    (ReturnPost i c s (word.setWidth 8).toNat) prefixRun
  rintro t ⟨regs,memory,pc⟩
  have loaded : t.data.dmem.loadInt t.data.regs.rsp.toBitVec 8 = some i.returnAddress.toNat := by
    rw [regs,memory]
    simpa [UInt64.toBitVec_add] using state.stack_words.2.2.2.2
  have executed := ret_trace fetch agree retOffset retMember t.data i.returnAddress loaded
    returnTarget (i.Writes c) rxSection
  have equal : (⟨t.data,AllowedipsImage.CommonBits.entry+.ofNat retOffset⟩ : MachineState) = t := by
    cases t; congr 1; exact pc.symm
  rw [equal] at executed
  apply eventually_weaken (historyStep fetch) _ _ _ _ executed
  rintro u ⟨machine,trace⟩
  refine ⟨?_,trace⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [machine]; rfl
  · simp only [machine,returnedState,regs,state.stack,UInt64.add_assoc]
    rfl
  · simp only [machine,returnedState,regs]
  · simp only [machine,returnedState,regs]
  · simp only [machine,returnedState,regs]
  · simp only [machine,returnedState,regs]
  · simp only [machine,returnedState,regs]
  · simp only [machine,returnedState,regs]
  · simp [machine,returnedState,regs,Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,
      BitVec.take,BitVec.drop,low8]
  · simpa only [machine,returnedState,memory] using state.ready.state
  · simp only [machine,returnedState,memory]
    intro _ _; rfl
  · simpa only [machine,returnedState,memory,state.stack] using state.ready.mapped

/-- History-preserving continuation composition at a proved body endpoint. -/
theorem finish_chain (fetch : Int64 → Option Decoded)
    (i : Input) (c : CommonBitsCoverage.Context) (s : MachineData)
    (start middle : Int64) (bx bp : UInt64) (answer : Nat) (rxSection : Nat)
    (firstSignature secondSignature : List EventView)
    (first : Eventually (historyStep fetch) (fun t =>
      BodyStep i c s middle bx bp t.machine ∧
      Local (i.Writes c) ⟨s,start⟩ rxSection firstSignature t) ⟨⟨s,start⟩,[⟨s,start⟩]⟩)
    (next : ∀ t : MachineData, BodyAt i c t → t.regs.rbx = bx → t.regs.rbp = bp →
      Eventually (historyStep fetch) (fun u => ReturnPost i c t answer u.machine ∧
        Local (i.Writes c) ⟨t,middle⟩ rxSection secondSignature u)
        ⟨⟨t,middle⟩,[⟨t,middle⟩]⟩) :
    Eventually (historyStep fetch) (fun t => ReturnPost i c s answer t.machine ∧
      Local (i.Writes c) ⟨s,start⟩ rxSection (firstSignature++secondSignature) t)
      ⟨⟨s,start⟩,[⟨s,start⟩]⟩ := by
  apply chain fetch (i.Writes c) ⟨s,start⟩ rxSection firstSignature secondSignature
    (BodyStep i c s middle bx bp) (ReturnPost i c s answer) first
  intro t post
  have run := next t.data post.body post.rbx post.rbp
  have equal : (⟨t.data,middle⟩ : MachineState) = t := by cases t; congr 1; exact post.atPC.symm
  rw [equal] at run
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
  rintro u ⟨result,trace⟩
  exact ⟨result.before post.r14 post.r15 post.frame,trace⟩

theorem simple_return_history (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (offset : Nat) (member : offset ∈ [0x43,0x6c])
    (i : Input) (c : CommonBitsCoverage.Context) (s : MachineData) (state : BodyAt i c s)
    (rxSection : Nat)
    (returnTarget : Int64.ofBitVec i.returnAddress.toBitVec = AllowedipsImage.Lookup.entry+0xea) :
    Eventually (historyStep fetch) (fun t => ReturnPost i c s (s.regs.get (.low .rbp .W8)).toNat t.machine ∧
      Local (i.Writes c) ⟨s,AllowedipsImage.CommonBits.entry+.ofNat offset⟩ rxSection [returnedView] t)
      ⟨⟨s,AllowedipsImage.CommonBits.entry+.ofNat offset⟩,[⟨s,AllowedipsImage.CommonBits.entry+.ofNat offset⟩]⟩ := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := state.stack_words
  have byte : ((s.regs.get (.low .rbp .W32)).setWidth 8).toNat =
      (s.regs.get (.low .rbp .W8)).toNat := by
    simp [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop,low_byte]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h | h
  · subst offset
    have executed := finish_from_restore fetch agree i c s state (AllowedipsImage.CommonBits.entry+0x43)
      0x4b (by decide) (s.regs.get (.low .rbp .W32)) rxSection returnTarget
      (return43_trace fetch agree s i.savedBx i.savedBp i.savedR12 i.savedR13 h0 h1 h2 h3 (i.Writes c) rxSection)
    simpa only [byte,show Int64.ofNat 67 = 67 from rfl,show Int64.ofNat 108 = 108 from rfl] using executed
  · subst offset
    have executed := finish_from_restore fetch agree i c s state (AllowedipsImage.CommonBits.entry+0x6c)
      0x74 (by decide) (s.regs.get (.low .rbp .W32)) rxSection returnTarget
      (return6c_trace fetch agree s i.savedBx i.savedBp i.savedR12 i.savedR13 h0 h1 h2 h3 (i.Writes c) rxSection)
    simpa only [byte,show Int64.ofNat 67 = 67 from rfl,show Int64.ofNat 108 = 108 from rfl] using executed

theorem ipv6_return_history (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch)
    (i : Input) (c : CommonBitsCoverage.Context) (s : MachineData) (state : BodyAt i c s)
    (rxSection : Nat)
    (returnTarget : Int64.ofBitVec i.returnAddress.toBitVec = AllowedipsImage.Lookup.entry+0xea) :
    Eventually (historyStep fetch) (fun t =>
      ReturnPost i c s (((s.regs.get (.low .rbp .W32))-(s.regs.get (.low .rbx .W32))).setWidth 8).toNat t.machine ∧
      Local (i.Writes c) ⟨s,AllowedipsImage.CommonBits.entry+0xb9⟩ rxSection [returnedView] t)
      ⟨⟨s,AllowedipsImage.CommonBits.entry+0xb9⟩,[⟨s,AllowedipsImage.CommonBits.entry+0xb9⟩]⟩ := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := state.stack_words
  exact finish_from_restore fetch agree i c s state (AllowedipsImage.CommonBits.entry+0xb9)
    0xc3 (by decide) _ rxSection returnTarget
    (return128_trace fetch agree s i.savedBx i.savedBp i.savedR12 i.savedR13 h0 h1 h2 h3 (i.Writes c) rxSection)

end Binary.CommonBits
