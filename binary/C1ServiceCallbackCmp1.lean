import C1ServiceCallbackText
import CallbackWrappers
import CallbackAgreement
import StatementC1CallbackImage

/-! `__sanitizer_cov_trace_cmp1` from the image's five instructions and the
landed proof of `write_comp_data`, in the form the allowed-IPs results consume
(`TrustBase.AllowedipsTraceCmp1Contract`). -/
namespace Binary.Callback.Cmp1
open TrustBase
local instance : Labels := Image.linkedLabels

/-- Inside the callback: the entry's stack pointer, outside the lookup image
and outside the allowed-IPs image. -/
def Interior (rsp : UInt64) (q : MachineState) : Prop :=
  leafGuard rsp q ∧ AllowedipsImage.fetch q.pc = none

theorem interior_step {fetch : Int64 → Option Decoded} {rsp : UInt64} {P : MachineState → Prop}
    {s : MachineData} {pc : Int64} {i : Instr} {n : Nat}
    (here : fetch pc = some ⟨i,n⟩) (positive : 0<n)
    (stack : s.regs.rsp=rsp) (outside : Image.fetch pc=none) (apart : AllowedipsImage.fetch pc = none)
    (run : (i.interp s ⟨pc,pc+.ofNat n⟩
      (fun d => .done ⟨d,pc+.ofNat n⟩) (fun p d => .done ⟨d,p⟩)).All
        (Eventually (guardedStep fetch (Interior rsp)) P)) :
    Eventually (guardedStep fetch (Interior rsp)) P ⟨s,pc⟩ := by
  apply step_cps
  exact ⟨⟨⟨stack,outside⟩,apart⟩,by simpa only [instructionStep,here] using And.intro positive run⟩

def entry : Int64 := .ofNat 0xffffffff810f4040

/-- One instruction of the entry: fetched through the agreement, inside the
interior, interpreted with the stepping set of the landed `callback_step`. -/
local macro "interior_instr" stub:ident : tactic => `(tactic|
  (apply interior_step ($stub _ _ (by rfl)) (by decide) (by rfl) (by rfl) (by rfl)
   simp only [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
     MachineData.load, MachineData.store, MachineData.set, MachineData.setReg,
     AddrExpr.interp, ConstExpr.interp, Reg64s.get, Reg64s.get64, Reg64s.set,
     Reg64s.set64, Reg.base, Reg.offset, BitVec.drop, BitVec.take,
     BitVec.toAddressSize, Effects.All]))

/-- `write_comp_data` from the state the entry leaves: the landed
`wrapper_body`, at the ambient decoder, with the interior kept out of the
allowed-IPs image. The entry's `xor` has changed the status flags, which the
body does not read. -/
theorem body (fetch : Int64 → Option Decoded) (services : ServiceDecoderAgreement fetch)
    (s : MachineData) (ra : UInt64) (status : StatusFlags)
    (ready : KcovReady .cmp1 ⟨s,entry⟩) (frame : EntryFrame ⟨s,entry⟩ ra) :
    Eventually (guardedStep fetch (Interior s.regs.rsp))
      (fun t => Returned ⟨s,entry⟩ t ra ∧
        EqualOutside (KcovWrites .cmp1 ⟨s,entry⟩) s.dmem t.data.dmem ∧
        KcovEffect .cmp1 ⟨s,entry⟩ t)
      ⟨{wrapperState .cmp1 s ra.toBitVec with status := status},.ofNat 0xffffffff810f3fb0⟩ := by
  have returnRead : load64 s.dmem s.regs.rsp.toBitVec=some ra.toBitVec := by
    simp [load64,frame.2]
  have run := wrapper_body (rsp := s.regs.rsp) .cmp1 (by decide) {s with status := status} entry ra
    ra.toBitVec returnRead ready frame rfl
  exact guarded_agreement services
    (change_guard (fun q inside => ⟨inside.1,Text.service_apart inside.2⟩) (Text.in_service run))

set_option maxRecDepth 4096 in -- the interpreter's terms for five instructions, as in the landed `cmp4_run`
set_option maxHeartbeats 2000000 in -- as above
theorem cmp1_run (fetch : Int64 → Option Decoded) (services : ServiceDecoderAgreement fetch)
    (stub : ∀ pc instruction, StatementC1CallbackImage.fetch pc = some instruction →
      fetch pc = some instruction)
    (s : MachineData) (ra : UInt64)
    (ready : KcovReady .cmp1 ⟨s,entry⟩) (frame : EntryFrame ⟨s,entry⟩ ra) :
    Eventually (guardedStep fetch (Interior s.regs.rsp))
      (fun t => Returned ⟨s,entry⟩ t ra ∧
        EqualOutside (KcovWrites .cmp1 ⟨s,entry⟩) s.dmem t.data.dmem ∧
        KcovEffect .cmp1 ⟨s,entry⟩ t)
      ⟨s,entry⟩ := by
  interior_instr stub
  simp [BitVec.signed,frame.2,Effects.All]
  interior_instr stub
  interior_instr stub
  interior_instr stub
  intro undefined
  interior_instr stub
  simp [RelRegOrMem.interp,ConstExpr.interp,Effects.All]
  have destination : label "L_ffffffff810f3fb0"=.ofNat 0xffffffff810f3fb0 := by decide +kernel
  rw [destination]
  have target : entry + 4 + 4 + 4 + 2 + 5 + (Int64.ofNat 18446744071579844528 - (entry + 4 + 4 + 4 + 2 + 5)) =
      .ofNat 0xffffffff810f3fb0 := by decide +kernel
  rw [target]
  simpa [wrapperState,KcovArgument,KcovRecordTag,Reg64s.get,Reg64s.get64,
    Reg.base,Reg.offset,BitVec.drop,BitVec.take] using
    body fetch services s ra _ ready frame

/-- The contract of the allowed-IPs results for `__sanitizer_cov_trace_cmp1`,
from agreement on the shared service bodies and on the entry's instructions. -/
theorem cmp1_contract (fetch : Int64 → Option Decoded) (services : ServiceDecoderAgreement fetch)
    (stub : ∀ pc instruction, StatementC1CallbackImage.fetch pc = some instruction →
      fetch pc = some instruction) : AllowedipsTraceCmp1Contract fetch := by
  rintro ⟨s,p⟩ ra pc ready frame
  change p=_ at pc
  subst p
  have history := guarded_history fetch _ _ _ (cmp1_run fetch services stub s ra ready frame) [] (by simp)
  apply eventually_weaken (historyStep fetch) _ _ _ _ history
  rintro t ⟨⟨returned,framed,effect⟩,interior⟩
  exact ⟨returned,framed,effect,fun q member => (interior q member).1.2,
    fun q member => (interior q member).2⟩

#print axioms cmp1_contract
end Binary.Callback.Cmp1
