import AllowedipsReturn

namespace Binary.Allowedips
open TrustBase CommonBits
local instance : Labels := Image.linkedLabels

theorem epilogue_trace (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch)
    (s : MachineData) (result bx bp r12 r13 r14 r15 ra : UInt64)
    (value : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some result.toNat)
    (h0 : s.dmem.loadInt (s.regs.rsp.toBitVec+32) 8 = some bx.toNat)
    (h1 : s.dmem.loadInt (s.regs.rsp.toBitVec+40) 8 = some bp.toNat)
    (h2 : s.dmem.loadInt (s.regs.rsp.toBitVec+48) 8 = some r12.toNat)
    (h3 : s.dmem.loadInt (s.regs.rsp.toBitVec+56) 8 = some r13.toNat)
    (h4 : s.dmem.loadInt (s.regs.rsp.toBitVec+64) 8 = some r14.toNat)
    (h5 : s.dmem.loadInt (s.regs.rsp.toBitVec+72) 8 = some r15.toNat)
    (h6 : s.dmem.loadInt (s.regs.rsp.toBitVec+80) 8 = some ra.toNat)
    (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t =>
      (t.machine.data.regs = {s.regs with
        rax := result,rbx := bx,rbp := bp,r12 := r12,r13 := r13,r14 := r14,r15 := r15,rsp := s.regs.rsp+88} ∧
       t.machine.data.dmem=s.dmem ∧ t.machine.pc= .ofBitVec ra.toBitVec) ∧
      Local (fun _ => False) ⟨s,AllowedipsImage.Lookup.entry+0x13c⟩ rxSection
        [(.returned "lookup",none)] t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x13c⟩,[⟨s,AllowedipsImage.Lookup.entry+0x13c⟩]⟩ := by
  have first := epilogue_prefix_trace fetch agree s result bx bp r12 r13 r14 r15
    value h0 h1 h2 h3 h4 h5 rxSection
  apply chain fetch (fun _ => False) ⟨s,AllowedipsImage.Lookup.entry+0x13c⟩ rxSection [] [(.returned "lookup",none)]
    (fun t => t.data.regs = {s.regs with
      rax := result,rbx := bx,rbp := bp,r12,r13,r14,r15,rsp := s.regs.rsp+80} ∧
      t.data.dmem=s.dmem ∧ t.pc=AllowedipsImage.Lookup.entry+0x14e)
    (fun t => t.data.regs = {s.regs with
      rax := result,rbx := bx,rbp := bp,r12,r13,r14,r15,rsp := s.regs.rsp+88} ∧
      t.data.dmem=s.dmem ∧ t.pc=.ofBitVec ra.toBitVec) first
  rintro ⟨middle,pc⟩ ⟨regs,memory,equal⟩
  dsimp only at regs memory equal
  subst pc
  have loaded : middle.dmem.loadInt middle.regs.rsp.toBitVec 8 = some ra.toNat := by
    rw [memory,regs]
    simpa only [UInt64.toBitVec_add,show (80 : UInt64).toBitVec=80#64 from rfl,BitVec.ofNat_eq_ofNat] using h6
  have final := ret_trace fetch agree middle ra loaded rxSection
  apply eventually_weaken (historyStep fetch) _ _ _ _ final
  rintro t ⟨machine,trace⟩
  refine ⟨⟨?_,?_,?_⟩,trace⟩
  · rw [machine]
    simp only [returnedData,regs,UInt64.add_assoc]
    rfl
  · rw [machine]; exact memory
  · rw [machine]

#print axioms epilogue_trace
end Binary.Allowedips
