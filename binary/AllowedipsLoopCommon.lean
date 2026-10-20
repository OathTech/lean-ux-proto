import AllowedipsLoopMatchExit
import CommonBitsEntryHistory

namespace Binary.AllowedipsLoop
open TrustBase Instrumentation LookupObservation
local instance : Labels := Image.linkedLabels

def commonEntry (s : MachineData) : MachineState :=
  calledState s (AllowedipsImage.Lookup.entry+0xea) AllowedipsImage.CommonBits.entry

theorem common_scratch_subset (s : MachineData) (coverage : CommonBitsCoverage.Context) (a : BitVec 64)
    (inside : CommonBits.EntryWrites coverage (commonEntry s).data a) : writes s.regs.rsp coverage a := by
  rcases inside with scratch | coverage
  · left
    obtain ⟨n,bound,address⟩ := scratch
    refine ⟨n,by omega,?_⟩
    simpa only [commonEntry,calledState,UInt64.toBitVec_sub,
      show (8 : UInt64).toBitVec = 8#64 from rfl,BitVec.sub_sub,
      show (8#64+40 : BitVec 64) = 48 from rfl] using address
  · exact .inr coverage

/-- The actual caller CALL and every common_bits instruction, including RET.
EntryAt is a physical description of the deterministic pushed state. -/
theorem common_local (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (contracts : CommonBits.Callbacks fetch) (s : MachineData)
    (i : CommonBits.Input) (coverage : CommonBitsCoverage.Context)
    (mapped : (s.dmem.loadInt (s.regs.rsp.toBitVec-8) 8).isSome = true)
    (entry : CommonBits.EntryAt i coverage (commonEntry s).data)
    (returnTarget : Int64.ofBitVec i.returnAddress.toBitVec = AllowedipsImage.Lookup.entry+0xea)
    (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t =>
      CommonBits.ReturnPost i coverage (CommonBits.prologueData (commonEntry s).data 8) i.result t.machine ∧
      CommonBits.Local (writes s.regs.rsp coverage) ⟨s,AllowedipsImage.Lookup.entry+0xe5⟩ rxSection
        ((.call "common_bits",none)::i.signature rxSection) t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0xe5⟩,[⟨s,AllowedipsImage.Lookup.entry+0xe5⟩]⟩ := by
  have called := historySteps_eventually fetch 1 _ _
    (call_instruction fetch (AllowedipsImage.Lookup.entry+0xe5) "L_ffffffff813a0950"
      (agree _ _ (by rfl)) s [⟨s,AllowedipsImage.Lookup.entry+0xe5⟩] mapped)
  have first : Eventually (historyStep fetch) (fun t => t.machine = commonEntry s ∧
      CommonBits.Local (writes s.regs.rsp coverage) ⟨s,AllowedipsImage.Lookup.entry+0xe5⟩ rxSection
        [(.call "common_bits",none)] t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0xe5⟩,[⟨s,AllowedipsImage.Lookup.entry+0xe5⟩]⟩ := by
    apply eventually_weaken (historyStep fetch) _ _ _ _ called
    rintro t ⟨machine,recorded⟩
    change t.machine = commonEntry s at machine
    have push : EqualOutside (writes s.regs.rsp coverage) s.dmem (commonEntry s).data.dmem := by
      intro a outside
      exact storeInt_frame s.dmem _ _ _ a (fun h => outside (callback_subset _ _ _ (.inl h)))
    refine ⟨machine,?_,?_,?_,?_,?_,?_⟩
    · rw [recorded]; rfl
    · rw [recorded]; simp
    · refine ⟨[LookupObservation.call "common_bits" (commonEntry s)],?_,rfl⟩
      rw [recorded,machine]
      rfl
    · rw [machine]; exact push
    · intro q member cut
      rw [recorded,machine] at member
      simp only [List.singleton_append,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · intro _ _; rfl
      · exact push
    · intro q member
      rw [recorded] at member
      simp only [List.singleton_append,List.dropLast_cons_cons,List.dropLast_singleton,List.mem_cons,List.not_mem_nil,or_false] at member
      subst q
      constructor <;> (dsimp only; decide)
  apply CommonBits.chain fetch (writes s.regs.rsp coverage) _ rxSection
    [(.call "common_bits",none)] (i.signature rxSection) (fun t => t = commonEntry s) _ first
  intro t equal
  rw [equal]
  have helper := CommonBits.entry_history fetch agree contracts i coverage (commonEntry s).data entry rxSection returnTarget
  apply eventually_weaken (historyStep fetch) _ _ _ _ helper
  rintro result ⟨post,trace⟩
  exact ⟨post,trace.mono (common_scratch_subset s coverage)⟩

#print axioms common_local
end Binary.AllowedipsLoop
