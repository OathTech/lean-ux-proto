import CommonBitsTrace
import CommonBitsHistory

namespace Binary.CommonBits
open LookupObservation
local instance : Labels := Image.linkedLabels

def decisionView (rxSection : Nat) (d : Leanux.Decision) (outcome : Bool) : EventView :=
  (.decision d, some {decision := d, outcome, netRx := rxSection})

theorem family32_trace (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AllowedipsDecoderAgreement fetch) (s : MachineData)
    (writes : BitVec 64 → Prop) (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t =>
      (t.machine.data.regs = s.regs ∧ t.machine.data.dmem = s.dmem ∧
       t.machine.pc = (if s.regs.get (.low .rbx .W8) == 32 then
         AllowedipsImage.CommonBits.entry+0x4c else AllowedipsImage.CommonBits.entry+0x26)) ∧
      Local writes ⟨s,AllowedipsImage.CommonBits.entry+0x21⟩ rxSection
        [decisionView rxSection .commonBits32 (s.regs.get (.low .rbx .W8) == 32)] t)
      ⟨⟨s,AllowedipsImage.CommonBits.entry+0x21⟩,[⟨s,AllowedipsImage.CommonBits.entry+0x21⟩]⟩ := by
  have executed := historySteps_eventually fetch 2 _ _
    (family32_history fetch agree s [⟨s,AllowedipsImage.CommonBits.entry+0x21⟩])
  apply eventually_weaken (historyStep fetch) _ _ _ _ executed
  rintro t ⟨regs,memory,pc,middle,recorded,midPC,midRegs,midMemory⟩
  refine ⟨⟨regs,memory,pc⟩, ?_⟩
  refine ⟨by rw [recorded]; rfl, by rw [recorded]; rfl, ?_, ?_, ?_, ?_⟩
  · refine ⟨[decision rxSection .commonBits32 (s.regs.get (.low .rbx .W8) == 32) t.machine], ?_, rfl⟩
    rw [recorded]
    have first : AllowedipsObservation.edge rxSection
        ⟨s,AllowedipsImage.CommonBits.entry+0x21⟩ middle = .ok [] := rfl
    have second : AllowedipsObservation.edge rxSection middle t.machine =
        .ok [decision rxSection .commonBits32 (s.regs.get (.low .rbx .W8) == 32) t.machine] := by
      unfold AllowedipsObservation.edge
      rw [midPC]
      change (do
        let choice ← LookupObservation.choice t.machine.pc
          (AllowedipsImage.CommonBits.entry+0x4c)
          (AllowedipsImage.CommonBits.entry+0x26)
        pure [decision rxSection .commonBits32 choice t.machine]) = _
      rw [pc]
      cases h : (s.regs.get (.low .rbx .W8) == 32) <;> simp [ LookupObservation.choice, AllowedipsImage.CommonBits.entry] <;> rfl
    simp only [List.singleton_append,observeHistory,first,second,]
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
    · subst q; change (AllowedipsImage.CommonBits.entry+_) ≠ _ ∧ (AllowedipsImage.CommonBits.entry+_) ≠ _; decide
    · subst q; change middle.pc ≠ _ ∧ middle.pc ≠ _; rw [midPC]; decide

theorem family128_trace (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AllowedipsDecoderAgreement fetch) (s : MachineData)
    (writes : BitVec 64 → Prop) (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t =>
      (t.machine.data.regs = s.regs ∧ t.machine.data.dmem = s.dmem ∧
       t.machine.pc = (if s.regs.get (.low .rbx .W8) == 128 then
         AllowedipsImage.CommonBits.entry+0x75 else AllowedipsImage.CommonBits.entry+0x3e)) ∧
      Local writes ⟨s,AllowedipsImage.CommonBits.entry+0x39⟩ rxSection
        [decisionView rxSection .commonBits128 (s.regs.get (.low .rbx .W8) == 128)] t)
      ⟨⟨s,AllowedipsImage.CommonBits.entry+0x39⟩,[⟨s,AllowedipsImage.CommonBits.entry+0x39⟩]⟩ := by
  have executed := historySteps_eventually fetch 2 _ _
    (family128_history fetch agree s [⟨s,AllowedipsImage.CommonBits.entry+0x39⟩])
  apply eventually_weaken (historyStep fetch) _ _ _ _ executed
  rintro t ⟨regs,memory,pc,middle,recorded,midPC,midRegs,midMemory⟩
  refine ⟨⟨regs,memory,pc⟩, ?_⟩
  refine ⟨by rw [recorded]; rfl, by rw [recorded]; rfl, ?_, ?_, ?_, ?_⟩
  · refine ⟨[decision rxSection .commonBits128 (s.regs.get (.low .rbx .W8) == 128) t.machine], ?_, rfl⟩
    rw [recorded]
    have first : AllowedipsObservation.edge rxSection
        ⟨s,AllowedipsImage.CommonBits.entry+0x39⟩ middle = .ok [] := rfl
    have second : AllowedipsObservation.edge rxSection middle t.machine =
        .ok [decision rxSection .commonBits128 (s.regs.get (.low .rbx .W8) == 128) t.machine] := by
      unfold AllowedipsObservation.edge
      rw [midPC]
      change (do
        let choice ← LookupObservation.choice t.machine.pc
          (AllowedipsImage.CommonBits.entry+0x75)
          (AllowedipsImage.CommonBits.entry+0x3e)
        pure [decision rxSection .commonBits128 choice t.machine]) = _
      rw [pc]
      cases h : (s.regs.get (.low .rbx .W8) == 128) <;> simp [ LookupObservation.choice, AllowedipsImage.CommonBits.entry] <;> rfl
    simp only [List.singleton_append,observeHistory,first,second,]
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
    · subst q; change (AllowedipsImage.CommonBits.entry+_) ≠ _ ∧ (AllowedipsImage.CommonBits.entry+_) ≠ _; decide
    · subst q; change middle.pc ≠ _ ∧ middle.pc ≠ _; rw [midPC]; decide

theorem high_equal_trace (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AllowedipsDecoderAgreement fetch) (s : MachineData)
    (writes : BitVec 64 → Prop) (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t =>
      (t.machine.data.regs = s.regs ∧ t.machine.data.dmem = s.dmem ∧
       t.machine.pc = (if s.regs.get (.low .rbx .W64) == s.regs.get (.low .rbp .W64) then
         AllowedipsImage.CommonBits.entry+0xc4 else AllowedipsImage.CommonBits.entry+0x93)) ∧
      Local writes ⟨s,AllowedipsImage.CommonBits.entry+0x8e⟩ rxSection
        [decisionView rxSection .fls128High (!(s.regs.get (.low .rbx .W64) == s.regs.get (.low .rbp .W64)))] t)
      ⟨⟨s,AllowedipsImage.CommonBits.entry+0x8e⟩,[⟨s,AllowedipsImage.CommonBits.entry+0x8e⟩]⟩ := by
  have executed := historySteps_eventually fetch 2 _ _
    (high_equal_history fetch agree s [⟨s,AllowedipsImage.CommonBits.entry+0x8e⟩])
  apply eventually_weaken (historyStep fetch) _ _ _ _ executed
  rintro t ⟨regs,memory,pc,middle,recorded,midPC,midRegs,midMemory⟩
  refine ⟨⟨regs,memory,pc⟩, ?_⟩
  refine ⟨by rw [recorded]; rfl, by rw [recorded]; rfl, ?_, ?_, ?_, ?_⟩
  · refine ⟨[decision rxSection .fls128High (!(s.regs.get (.low .rbx .W64) == s.regs.get (.low .rbp .W64))) t.machine], ?_, rfl⟩
    rw [recorded]
    have first : AllowedipsObservation.edge rxSection
        ⟨s,AllowedipsImage.CommonBits.entry+0x8e⟩ middle = .ok [] := rfl
    have second : AllowedipsObservation.edge rxSection middle t.machine =
        .ok [decision rxSection .fls128High (!(s.regs.get (.low .rbx .W64) == s.regs.get (.low .rbp .W64))) t.machine] := by
      unfold AllowedipsObservation.edge
      rw [midPC]
      change (do
        let choice ← LookupObservation.choice t.machine.pc
          (AllowedipsImage.CommonBits.entry+0x93)
          (AllowedipsImage.CommonBits.entry+0xc4)
        pure [decision rxSection .fls128High choice t.machine]) = _
      rw [pc]
      cases h : (s.regs.get (.low .rbx .W64) == s.regs.get (.low .rbp .W64)) <;> simp [ LookupObservation.choice, AllowedipsImage.CommonBits.entry] <;> rfl
    simp only [List.singleton_append,observeHistory,first,second,]
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
    · subst q; change (AllowedipsImage.CommonBits.entry+_) ≠ _ ∧ (AllowedipsImage.CommonBits.entry+_) ≠ _; decide
    · subst q; change middle.pc ≠ _ ∧ middle.pc ≠ _; rw [midPC]; decide

end Binary.CommonBits
