import CommonBitsEntryState
import CommonBitsPathsHistory

namespace Binary.CommonBits
open TrustBase LookupObservation
local instance : Labels := Image.linkedLabels

theorem Local.mono {small large initial rx signature final}
    (trace : Local small initial rx signature final)
    (subset : ∀ a, small a → large a) : Local large initial rx signature final := by
  exact {trace with
    frame := fun a outside => trace.frame a (fun h => outside (subset a h))
    cuts := fun q member cut a outside => trace.cuts q member cut a (fun h => outside (subset a h))}

/-- Actual save/copy instructions, retaining every intermediate memory. -/
theorem entry_prefix_history (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (i : Input) (c : CommonBitsCoverage.Context)
    (s : MachineData) (entry : EntryAt i c s) (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t =>
      t.machine = ⟨prologueData s 8,AllowedipsImage.CommonBits.entry+0x10⟩ ∧
      Local (EntryWrites c s) ⟨s,AllowedipsImage.CommonBits.entry⟩ rxSection [] t)
      ⟨⟨s,AllowedipsImage.CommonBits.entry⟩,[⟨s,AllowedipsImage.CommonBits.entry⟩]⟩ := by
  have executed := historySteps_eventually fetch 8 _ _
    (prologue_prefix_history fetch agree s [⟨s,AllowedipsImage.CommonBits.entry⟩] entry.mapped)
  apply eventually_weaken (historyStep fetch) _ _ _ _ executed
  rintro t ⟨machine,recorded⟩
  have frame (n : Nat) (bound : savedCount n ≤ 5) :
      EqualOutside (EntryWrites c s) s.dmem (prologueData s n).dmem := by
    intro a outside
    exact saveMemory_frame s (savedCount n) bound a (fun h => outside (.inl h))
  refine ⟨machine,?_,?_,?_,?_,?_,?_⟩
  · rw [recorded]; rfl
  · rw [recorded,machine]; rfl
  · refine ⟨[],?_,rfl⟩
    rw [recorded]
    rfl
  · rw [machine]; exact frame 8 (by decide)
  · intro q member cut
    rw [recorded] at member
    simp only [prologueStates,List.take_succ_cons,List.take_zero,List.singleton_append,
      List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h | h | h | h | h | h | h | h | h
    · subst q; intro _ _; rfl
    all_goals subst q; exact frame _ (by decide)
  · intro q member
    rw [recorded] at member
    simp only [prologueStates,List.take_succ_cons,List.take_zero,List.singleton_append,
      List.dropLast_cons_cons,List.dropLast_singleton,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h | h | h | h | h | h | h | h
    all_goals subst q; constructor <;> (dsimp only; decide)

/-- Body-entry callback composed with the complete body, including RET. -/
theorem after_saves_history (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (contracts : Callbacks fetch)
    (i : Input) (c : CommonBitsCoverage.Context) (s : MachineData)
    (entry : EntryAt i c s) (rxSection : Nat)
    (returnTarget : Int64.ofBitVec i.returnAddress.toBitVec = AllowedipsImage.Lookup.entry+0xea) :
    Eventually (historyStep fetch) (fun t =>
      ReturnPost i c (prologueData s 8) i.result t.machine ∧
      Local (i.Writes c) ⟨prologueData s 8,AllowedipsImage.CommonBits.entry+0x10⟩
        rxSection (i.signature rxSection) t)
      ⟨⟨prologueData s 8,AllowedipsImage.CommonBits.entry+0x10⟩,
       [⟨prologueData s 8,AllowedipsImage.CommonBits.entry+0x10⟩]⟩ := by
  have here := agree _ _ (show AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry+0x10) =
    some ⟨Instrumentation.callInstruction "L_ffffffff810f31f0",5⟩ from rfl)
  have call := callback_body_trace fetch _ "L_ffffffff810f31f0" here .pc contracts.pc
    i c entry.bodySeparate (prologueData s 8) entry.body rxSection (by intros; rfl) (by decide)
  have called : Eventually (historyStep fetch) (fun t =>
      BodyStep i c (prologueData s 8) (AllowedipsImage.CommonBits.entry+0x15)
        (prologueData s 8).regs.rbx (prologueData s 8).regs.rbp t.machine ∧
      Local (i.Writes c) ⟨prologueData s 8,AllowedipsImage.CommonBits.entry+0x10⟩ rxSection [] t)
      ⟨⟨prologueData s 8,AllowedipsImage.CommonBits.entry+0x10⟩,
       [⟨prologueData s 8,AllowedipsImage.CommonBits.entry+0x10⟩]⟩ := call
  apply finish_chain fetch i c (prologueData s 8) _ _ _ _ _ rxSection [] (i.signature rxSection) called
  intro t state bx bp
  apply body_history fetch agree contracts i c entry.bodySeparate t state rxSection returnTarget
  · simpa only [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,bx] using entry.family_bytes.1
  · simpa only [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,bp] using entry.family_bytes.2

/-- Complete helper execution from its actual ABI entry. The body post refers
    to the deterministic save state; the Local frame covers the entire invocation. -/
theorem entry_history (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (contracts : Callbacks fetch)
    (i : Input) (c : CommonBitsCoverage.Context) (s : MachineData)
    (entry : EntryAt i c s) (rxSection : Nat)
    (returnTarget : Int64.ofBitVec i.returnAddress.toBitVec = AllowedipsImage.Lookup.entry+0xea) :
    Eventually (historyStep fetch) (fun t =>
      ReturnPost i c (prologueData s 8) i.result t.machine ∧
      Local (EntryWrites c s) ⟨s,AllowedipsImage.CommonBits.entry⟩ rxSection (i.signature rxSection) t)
      ⟨⟨s,AllowedipsImage.CommonBits.entry⟩,[⟨s,AllowedipsImage.CommonBits.entry⟩]⟩ := by
  apply chain fetch (EntryWrites c s) ⟨s,AllowedipsImage.CommonBits.entry⟩ rxSection [] (i.signature rxSection)
    (fun t => t = ⟨prologueData s 8,AllowedipsImage.CommonBits.entry+0x10⟩)
    (ReturnPost i c (prologueData s 8) i.result) (entry_prefix_history fetch agree i c s entry rxSection)
  intro t equal
  rw [equal]
  apply eventually_weaken (historyStep fetch) _ _ _ _
    (after_saves_history fetch agree contracts i c s entry rxSection returnTarget)
  rintro u ⟨post,trace⟩
  exact ⟨post,trace.mono entry.writes_subset⟩

#print axioms entry_history
end Binary.CommonBits
