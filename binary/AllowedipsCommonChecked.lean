import CommonBitsCheckProof
import CommonBitsSequentialCall
import AllowedipsLoopInput

namespace Binary.Pair.Allowedips
open TrustBase AllowedipsMutationImage
local instance : Labels := Image.linkedLabels

theorem common_input_result (s : MachineData) (bits stored query : Nat) (returnPC : Int64)
    (family : bits=32 ∨ bits=128) (storedBound : stored<2^bits) (queryBound : query<2^bits) :
    (Common.callInput s bits stored query returnPC).result=AllowedipsRelation.common bits stored query := by
  change (AllowedipsLoop.input s bits stored query).result=_
  exact AllowedipsLoop.input_result s bits stored query family storedBound queryBound

/-- Both insertion helper calls use the same tested readiness assertion and
complete helper theorem. The differing return PCs are ordinary caller data. -/
theorem common_checked (fetch : Int64 → Option Decoded)
    (decoder : AllowedipsDecoderAgreement fetch)
    (mutation : AllowedipsMutationDecoderAgreement fetch)
    (callbacks : CommonBits.Callbacks fetch)
    (pc : Int64) (site : pc=Add.entry+0x9c ∨ pc=Add.entry+0x255)
    (c : CommonBitsCoverage.Context) (s : MachineData) (bits stored query : Nat)
    (family : bits=32 ∨ bits=128) (storedBound : stored<2^bits) (queryBound : query<2^bits)
    (checked : Common.callerCheck (Common.callInput s bits stored query (pc+5)) c s (pc+5)=true) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=pc+5 ∧ t.data.regs.rsp=s.regs.rsp ∧
      t.data.regs.rbx=s.regs.rbx ∧ t.data.regs.rbp=s.regs.rbp ∧
      t.data.regs.r12=s.regs.r12 ∧ t.data.regs.r13=s.regs.r13 ∧
      t.data.regs.r14=s.regs.r14 ∧ t.data.regs.r15=s.regs.r15 ∧
      (t.data.regs.get (.low .rax .W8)).toNat=AllowedipsRelation.common bits stored query ∧
      c.At t.data.dmem ∧
      EqualOutside (fun a => CommonBits.CallerScratch s a ∨ c.writes a) s.dmem t.data.dmem ∧
      ∀ n < 6, (t.data.dmem.loadInt (s.regs.rsp.toBitVec-.ofNat 64 ((n+1)*8)) 8).isSome=true)
      ⟨s,pc⟩ := by
  have here : fetch pc=some ⟨Instrumentation.callInstruction "L_ffffffff813a0950",5⟩ := by
    rcases site with rfl | rfl
    all_goals exact mutation.add _ _ (by rfl)
  simpa only [common_input_result s bits stored query (pc+5) family storedBound queryBound] using
    CommonBits.Sequential.call_run fetch decoder callbacks pc here
      (Common.callInput s bits stored query (pc+5)) c s (Common.callerCheck_sound checked)

#print axioms common_checked
end Binary.Pair.Allowedips
