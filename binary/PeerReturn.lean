import StackFrame
import TrustBase
import ImageLayout

namespace Binary.PeerGet
local instance : Labels := Image.linkedLabels

/-- Execute the actual six POPs and RET from the restored stack window.
    Callback scratch below that window may have been overwritten repeatedly. -/
theorem return_from_saved (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch)
    (initial : MachineState) (body : MachineData) (returnAddress : UInt64)
    (entry : TrustBase.EntryFrame initial returnAddress)
    (sp : body.regs.rsp = initial.data.regs.rsp - 48)
    (writes : BitVec 64 → Prop)
    (frame : EqualOutside writes (saveMemory initial.data 7) body.dmem)
    (separate : ∀ address, InRange (initial.data.regs.rsp.toBitVec - 48) 56 address →
      ¬writes address) :
    Eventually (instructionStep fetch)
      (fun final => TrustBase.Returned initial final returnAddress ∧
        final.data.regs.rax = body.regs.rbx ∧ final.data.dmem = body.dmem)
      ⟨body, Image.PeerGet.entry + 0xa2⟩ := by
  have base : body.regs.rsp.toBitVec = initial.data.regs.rsp.toBitVec - 48 := by
    simp [sp]
  have read (j : Nat) (bound : j ≤ 6) :
      (saveMemory initial.data 7).loadInt
        (body.regs.rsp.toBitVec + .ofNat 64 (8*j)) 8 =
      body.dmem.loadInt (body.regs.rsp.toBitVec + .ofNat 64 (8*j)) 8 := by
    apply frame.loadInt
    intro byte byteBound
    apply separate
    refine ⟨8*j+byte, by omega, ?_⟩
    simp only [base, BitVec.ofNat_add, BitVec.add_assoc]
  have saved (j : Nat) (bound : j < 6) :
      body.dmem.loadInt (body.regs.rsp.toBitVec + .ofNat 64 (8*j)) 8 =
        some (((savedWords initial.data)[5-j]?.getD 0).toNat : Int) := by
    have index : 5-(5-j) = j := by omega
    have pushed := saveMemory_read initial.data 7 (5-j) (by decide) (by omega)
    rw [slot_restore_window initial.data (5-j) (by omega), index, ← base] at pushed
    exact (read j (by omega)).symm.trans pushed
  have original : body.dmem.loadInt (body.regs.rsp.toBitVec + 48) 8 =
      some (returnAddress.toNat : Int) := by
    have framed := read 6 (by decide)
    simp only [Nat.reduceMul] at framed
    have returned := saveMemory_return initial.data 7 (by decide)
    rw [entry.2] at returned
    have address : body.regs.rsp.toBitVec + BitVec.ofNat 64 48 = initial.data.regs.rsp.toBitVec := by
      rw [base]
      exact BitVec.sub_add_cancel _ _
    rw [address] at framed
    simpa only [base, BitVec.sub_add_cancel] using framed.symm.trans returned
  have code := epilogue body initial.data.regs.rbx initial.data.regs.rbp
    initial.data.regs.r12 initial.data.regs.r13 initial.data.regs.r14 initial.data.regs.r15
    returnAddress
    (by simpa [savedWords] using saved 0 (by decide))
    (by simpa [savedWords] using saved 1 (by decide))
    (by simpa [savedWords] using saved 2 (by decide))
    (by simpa [savedWords] using saved 3 (by decide))
    (by simpa [savedWords] using saved 4 (by decide))
    (by simpa [savedWords] using saved 5 (by decide)) original
  have executed := region_eventually (Image.PeerGet_ra2_layout.agreement agree) body _ code
  apply eventually_weaken (instructionStep fetch) _ _ _ _ executed
  rintro final ⟨regs, memory, pc⟩
  refine ⟨⟨pc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, memory⟩
  · simp only [regs, sp]
    change initial.data.regs.rsp - 48 + 56 = initial.data.regs.rsp + 8
    apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_add, UInt64.toBitVec_sub]
    change initial.data.regs.rsp.toBitVec - 48 + 56 = initial.data.regs.rsp.toBitVec + 8
    rw [show (56 : BitVec 64) = 48+8 from rfl, ← BitVec.add_assoc, BitVec.sub_add_cancel]
  all_goals simp only [regs]

#print axioms return_from_saved
end Binary.PeerGet
