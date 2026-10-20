import CommonBitsEntryState
import CommonBitsSequentialPaths

namespace Binary.CommonBits.Sequential
open TrustBase
local instance : Labels := Image.linkedLabels

private theorem first_callback_layout :
    LaidOut AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry+0x10)
      AllowedipsImage.CommonBits.r26 := by binary_layout

theorem after_saves_run (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (contracts : Callbacks fetch)
    (i : Input) (c : CommonBitsCoverage.Context) (s : MachineData)
    (entry : EntryAt i c s) :
    Eventually (instructionStep fetch) (ReturnPost i c (prologueData s 8) i.result)
      ⟨prologueData s 8,AllowedipsImage.CommonBits.entry+0x10⟩ := by
  apply chain_step fetch i c (prologueData s 8) _ _ _ _ _
    (trace_step fetch agree contracts 0x10 first_callback_layout
      i c entry.bodySeparate (prologueData s 8) entry.body)
  intro t state bx bp
  apply body_run fetch agree contracts i c entry.bodySeparate t state
  · simpa only [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,bx] using entry.family_bytes.1
  · simpa only [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,bp] using entry.family_bytes.2

/-- A complete helper invocation, independent of the caller's return address.
    The frame includes its actual saves and shared instrumentation writes. -/
structure CallPost (i : Input) (c : CommonBitsCoverage.Context)
    (before : MachineData) (after : MachineState) : Prop where
  pc : after.pc = .ofBitVec i.returnAddress.toBitVec
  stack : after.data.regs.rsp = before.regs.rsp+8
  rbx : after.data.regs.rbx = before.regs.rbx
  rbp : after.data.regs.rbp = before.regs.rbp
  r12 : after.data.regs.r12 = before.regs.r12
  r13 : after.data.regs.r13 = before.regs.r13
  r14 : after.data.regs.r14 = before.regs.r14
  r15 : after.data.regs.r15 = before.regs.r15
  result : (after.data.regs.get (.low .rax .W8)).toNat = i.result
  coverage : c.At after.data.dmem
  frame : EqualOutside (EntryWrites c before) before.dmem after.data.dmem

theorem entry_run (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (contracts : Callbacks fetch)
    (i : Input) (c : CommonBitsCoverage.Context) (s : MachineData)
    (entry : EntryAt i c s) :
    Eventually (instructionStep fetch) (fun t =>
      CallPost i c s t ∧ ReturnPost i c (prologueData s 8) i.result t)
      ⟨s,AllowedipsImage.CommonBits.entry⟩ := by
  have savedRun := history_project fetch _ _ (historySteps_eventually fetch 8 _ _
    (prologue_prefix_history fetch agree s [] entry.mapped))
  apply eventually_trans (instructionStep fetch) _ _ _ savedRun
  rintro t ⟨history, machine, _⟩
  change t = _ at machine
  rw [machine]
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (after_saves_run fetch agree contracts i c s entry)
  intro final post
  refine ⟨?_,post⟩
  refine ⟨post.pc,?_,post.rbx.trans entry.savedBx,post.rbp.trans entry.savedBp,
    post.r12.trans entry.savedR12,post.r13.trans entry.savedR13,post.r14,post.r15,
    post.result,post.coverage,?_⟩
  · rw [post.stack,entry.stack]
    change s.regs.rsp-32+40 = s.regs.rsp+8
    apply UInt64.eq_of_toBitVec_eq
    change s.regs.rsp.toBitVec-32+40 = s.regs.rsp.toBitVec+8
    bv_omega
  · intro a outside
    have saved := saveMemory_frame s 4 (by decide) a (fun h => outside (.inl h))
    exact saved.trans (post.frame a (fun h => outside (entry.writes_subset a h)))

#print axioms entry_run
end Binary.CommonBits.Sequential
