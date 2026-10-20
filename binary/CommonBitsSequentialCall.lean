import CommonBitsSequentialEntry
import CommonBitsCallerState
import SequentialExecution

namespace Binary.CommonBits.Sequential
open TrustBase Instrumentation
local instance : Labels := Image.linkedLabels

/-- Reusable caller contract: actual CALL, complete common_bits, actual RET.
    Scratch readability is exported for the caller's next instrumentation call. -/
theorem call_run (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (contracts : Callbacks fetch)
    (pc : Int64) (here : fetch pc=some ⟨callInstruction "L_ffffffff813a0950",5⟩)
    (i : Input) (c : CommonBitsCoverage.Context) (s : MachineData)
    (caller : CallerAt i c s (pc+5)) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=pc+5 ∧ t.data.regs.rsp=s.regs.rsp ∧
      t.data.regs.rbx=s.regs.rbx ∧ t.data.regs.rbp=s.regs.rbp ∧
      t.data.regs.r12=s.regs.r12 ∧ t.data.regs.r13=s.regs.r13 ∧
      t.data.regs.r14=s.regs.r14 ∧ t.data.regs.r15=s.regs.r15 ∧
      (t.data.regs.get (.low .rax .W8)).toNat=i.result ∧ c.At t.data.dmem ∧
      EqualOutside (fun a => CallerScratch s a ∨ c.writes a) s.dmem t.data.dmem ∧
      ∀ n < 6, (t.data.dmem.loadInt (s.regs.rsp.toBitVec-.ofNat 64 ((n+1)*8)) 8).isSome=true)
      ⟨s,pc⟩ := by
  have called : Eventually (instructionStep fetch)
      (fun t => t=helperEntry s (pc+5)) ⟨s,pc⟩ := Sequential.forget
    (historySteps_eventually fetch 1 _ _
      (call_instruction fetch pc "L_ffffffff813a0950" here s [] caller.callMapped))
    (fun _ result => result.1)
  apply eventually_trans (instructionStep fetch) _ _ _ called
  intro t machine
  change t=helperEntry s (pc+5) at machine
  rw [machine]
  have run := entry_run fetch agree contracts i c (helperEntry s (pc+5)).data caller.entry
  apply eventually_weaken (instructionStep fetch) _ _ _ _ run
  rintro final ⟨post,body⟩
  refine ⟨post.pc.trans caller.returnTarget,?_,post.rbx,post.rbp,post.r12,post.r13,
    post.r14,post.r15,post.result,post.coverage,?_,caller.finalMapped body⟩
  · rw [post.stack]
    change s.regs.rsp-8+8=s.regs.rsp
    exact UInt64.sub_add_cancel _ _
  · intro a outside
    have pushOutside : ¬InRange (s.regs.rsp.toBitVec-8) 8 a := by
      rintro ⟨n,bound,atByte⟩
      apply outside
      left
      refine ⟨40+n,by omega,?_⟩
      have base : s.regs.rsp.toBitVec-48+40#64=s.regs.rsp.toBitVec-8 := by bv_omega
      simpa only [BitVec.ofNat_add,←BitVec.add_assoc,base] using atByte
    exact (storeInt_frame s.dmem _ _ _ a pushOutside).trans
      (post.frame a (fun h => outside (caller.entryWrites_subset a h)))

#print axioms call_run
end Binary.CommonBits.Sequential
