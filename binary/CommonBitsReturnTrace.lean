import CommonBitsTrace
import CommonBitsFinish

namespace Binary.CommonBits
open TrustBase LookupObservation
local instance : Labels := Image.linkedLabels

def returnedView : EventView := (.returned "common_bits",none)

def returnedState (s : MachineData) (ra : UInt64) : MachineState :=
  ⟨{s with regs := {s.regs with rsp := s.regs.rsp+8}},.ofBitVec ra.toBitVec⟩

theorem ret_trace (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (offset : Nat) (member : offset ∈ [0x4b,0x74,0xc3])
    (s : MachineData) (ra : UInt64)
    (loaded : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some ra.toNat)
    (target : Int64.ofBitVec ra.toBitVec = AllowedipsImage.Lookup.entry+0xea)
    (writes : BitVec 64 → Prop) (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t =>
      t.machine = returnedState s ra ∧
      Local writes ⟨s,AllowedipsImage.CommonBits.entry+.ofNat offset⟩ rxSection [returnedView] t)
      ⟨⟨s,AllowedipsImage.CommonBits.entry+.ofNat offset⟩,[⟨s,AllowedipsImage.CommonBits.entry+.ofNat offset⟩]⟩ := by
  have here : fetch (AllowedipsImage.CommonBits.entry+.ofNat offset) =
      some ⟨.regular .W64 .W64 .ret,1⟩ := by
    apply agree
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h | h | h
    all_goals subst offset; rfl
  have one : instructionStep fetch ⟨s,AllowedipsImage.CommonBits.entry+.ofNat offset⟩
      (fun t => t = returnedState s ra) := by
    rw [instructionStep,here]
    refine ⟨by decide,?_⟩
    simp [Instr.interp,Operation.interp,MachineData.load,Effects.All,
      Reg64s.get64,Reg64s.set64,loaded,returnedState]
  have executed := historySteps_eventually fetch 1 _ _
    (instruction_history fetch _ [⟨s,AllowedipsImage.CommonBits.entry+.ofNat offset⟩] _ one)
  apply eventually_weaken (historyStep fetch) _ _ _ _ executed
  rintro t ⟨machine,recorded⟩
  refine ⟨machine,?_,?_,?_,?_,?_,?_⟩
  · rw [recorded]; rfl
  · rw [recorded]; rfl
  · refine ⟨[returned "common_bits" t.machine],?_,rfl⟩
    have edge : AllowedipsObservation.edge rxSection
        ⟨s,AllowedipsImage.CommonBits.entry+.ofNat offset⟩ t.machine =
        .ok [returned "common_bits" t.machine] := by
      have destination : t.machine.pc = AllowedipsImage.Lookup.entry+0xea := by rw [machine]; exact target
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with h | h | h
      all_goals subst offset
      all_goals unfold AllowedipsObservation.edge
      all_goals change (if t.machine.pc != AllowedipsImage.Lookup.entry+0xea then _ else _) = _
      all_goals simp [destination]
      all_goals rfl
    rw [recorded]
    simp only [List.singleton_append,observeHistory,edge]
    rfl
  · rw [machine]; intro _ _; rfl
  · intro q present cut
    rw [recorded] at present
    simp only [List.singleton_append,List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with a | b
    · subst q; intro _ _; rfl
    · subst q; rw [machine]; intro _ _; rfl
  · intro q present
    rw [recorded] at present
    simp only [List.singleton_append,List.dropLast_cons_cons,List.dropLast_singleton,
      List.mem_cons,List.not_mem_nil,or_false] at present
    subst q
    change (AllowedipsImage.CommonBits.entry+.ofNat offset) ≠ _ ∧
      (AllowedipsImage.CommonBits.entry+.ofNat offset) ≠ _
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h | h | h
    all_goals subst offset; decide

end Binary.CommonBits
