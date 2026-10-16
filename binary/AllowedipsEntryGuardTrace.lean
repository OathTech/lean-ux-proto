import CommonBitsTrace
import AllowedipsHistory
import CommonBitsGuardTrace

namespace Binary.AllowedipsEntry
open LookupObservation CommonBits
local instance : Labels := Image.linkedLabels

theorem family32_trace (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AllowedipsDecoderAgreement fetch) (s : MachineData)
    (writes : BitVec 64 → Prop) (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t =>
      (t.machine.data.regs = s.regs ∧ t.machine.data.dmem = s.dmem ∧
       t.machine.pc = (if s.regs.get (.low .rbx .W8) == 32 then
         AllowedipsImage.Lookup.entry+0x171 else AllowedipsImage.Lookup.entry+0x47)) ∧
      Local writes ⟨s,AllowedipsImage.Lookup.entry+0x3e⟩ rxSection
        [decisionView rxSection .swapEndian32 (s.regs.get (.low .rbx .W8) == 32)] t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x3e⟩,[⟨s,AllowedipsImage.Lookup.entry+0x3e⟩]⟩ := by
  have executed := historySteps_eventually fetch 2 _ _
    (Allowedips.family32_history fetch agree s [⟨s,AllowedipsImage.Lookup.entry+0x3e⟩])
  apply eventually_weaken (historyStep fetch) _ _ _ _ executed
  rintro t ⟨regs,memory,pc,middle,recorded,midPC,midRegs,midMemory⟩
  refine ⟨⟨regs,memory,pc⟩, ?_⟩
  refine ⟨by rw [recorded]; rfl, by rw [recorded]; rfl, ?_, ?_, ?_, ?_⟩
  · refine ⟨[decision rxSection .swapEndian32 (s.regs.get (.low .rbx .W8) == 32) t.machine], ?_, rfl⟩
    rw [recorded]
    have first : AllowedipsObservation.edge rxSection
        ⟨s,AllowedipsImage.Lookup.entry+0x3e⟩ middle = .ok [] := rfl
    have second : AllowedipsObservation.edge rxSection middle t.machine =
        .ok [decision rxSection .swapEndian32 (s.regs.get (.low .rbx .W8) == 32) t.machine] := by
      unfold AllowedipsObservation.edge
      rw [midPC]
      change (do
        let choice ← LookupObservation.choice t.machine.pc
          (AllowedipsImage.Lookup.entry+0x171)
          (AllowedipsImage.Lookup.entry+0x47)
        pure [decision rxSection .swapEndian32 choice t.machine]) = _
      rw [pc]
      cases h : (s.regs.get (.low .rbx .W8) == 32) <;> simp [h, LookupObservation.choice, AllowedipsImage.Lookup.entry] <;> rfl
    simp only [List.singleton_append,observeHistory,first,second,List.nil_append,List.append_nil]
    rfl
  · rw [memory]; intro _ _; rfl
  · intro q member cut
    rw [recorded] at member
    simp only [List.singleton_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with first | middleEq | last
    · subst q; intro _ _; rfl
    · subst q; rw [midMemory]; intro _ _; rfl
    · subst q; rw [memory]; intro _ _; rfl
  · intro q member
    rw [recorded] at member
    simp only [List.singleton_append,List.dropLast_cons_cons,List.dropLast_singleton,
      List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with first | middleEq
    · subst q; change (AllowedipsImage.Lookup.entry+_) ≠ _ ∧ (AllowedipsImage.Lookup.entry+_) ≠ _; decide
    · subst q; change middle.pc ≠ _ ∧ middle.pc ≠ _; rw [midPC]; decide

theorem family128_trace (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AllowedipsDecoderAgreement fetch) (s : MachineData)
    (writes : BitVec 64 → Prop) (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t =>
      (t.machine.data.regs = s.regs ∧ t.machine.data.dmem = s.dmem ∧
       t.machine.pc = (if s.regs.get (.low .rbx .W8) == 128 then
         AllowedipsImage.Lookup.entry+0x14f else AllowedipsImage.Lookup.entry+0x61)) ∧
      Local writes ⟨s,AllowedipsImage.Lookup.entry+0x58⟩ rxSection
        [decisionView rxSection .swapEndian128 (s.regs.get (.low .rbx .W8) == 128)] t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x58⟩,[⟨s,AllowedipsImage.Lookup.entry+0x58⟩]⟩ := by
  have executed := historySteps_eventually fetch 2 _ _
    (Allowedips.family128_history fetch agree s [⟨s,AllowedipsImage.Lookup.entry+0x58⟩])
  apply eventually_weaken (historyStep fetch) _ _ _ _ executed
  rintro t ⟨regs,memory,pc,middle,recorded,midPC,midRegs,midMemory⟩
  refine ⟨⟨regs,memory,pc⟩, ?_⟩
  refine ⟨by rw [recorded]; rfl, by rw [recorded]; rfl, ?_, ?_, ?_, ?_⟩
  · refine ⟨[decision rxSection .swapEndian128 (s.regs.get (.low .rbx .W8) == 128) t.machine], ?_, rfl⟩
    rw [recorded]
    have first : AllowedipsObservation.edge rxSection
        ⟨s,AllowedipsImage.Lookup.entry+0x58⟩ middle = .ok [] := rfl
    have second : AllowedipsObservation.edge rxSection middle t.machine =
        .ok [decision rxSection .swapEndian128 (s.regs.get (.low .rbx .W8) == 128) t.machine] := by
      unfold AllowedipsObservation.edge
      rw [midPC]
      change (do
        let choice ← LookupObservation.choice t.machine.pc
          (AllowedipsImage.Lookup.entry+0x14f)
          (AllowedipsImage.Lookup.entry+0x61)
        pure [decision rxSection .swapEndian128 choice t.machine]) = _
      rw [pc]
      cases h : (s.regs.get (.low .rbx .W8) == 128) <;> simp [h, LookupObservation.choice, AllowedipsImage.Lookup.entry] <;> rfl
    simp only [List.singleton_append,observeHistory,first,second,List.nil_append,List.append_nil]
    rfl
  · rw [memory]; intro _ _; rfl
  · intro q member cut
    rw [recorded] at member
    simp only [List.singleton_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with first | middleEq | last
    · subst q; intro _ _; rfl
    · subst q; rw [midMemory]; intro _ _; rfl
    · subst q; rw [memory]; intro _ _; rfl
  · intro q member
    rw [recorded] at member
    simp only [List.singleton_append,List.dropLast_cons_cons,List.dropLast_singleton,
      List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with first | middleEq
    · subst q; change (AllowedipsImage.Lookup.entry+_) ≠ _ ∧ (AllowedipsImage.Lookup.entry+_) ≠ _; decide
    · subst q; change middle.pc ≠ _ ∧ middle.pc ≠ _; rw [midPC]; decide


#print axioms family32_trace
#print axioms family128_trace
end Binary.AllowedipsEntry
