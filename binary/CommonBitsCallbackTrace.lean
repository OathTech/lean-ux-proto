import CommonBitsTrace

namespace Binary.CommonBits
open TrustBase LookupObservation Instrumentation
local instance : Labels := Image.linkedLabels

/-- The actual callback CALL and its named service retain one local physical
    history. All service-internal states remain recorded but cannot be cuts. -/
theorem callback_trace (fetch : Int64 → Option Decoded) (pc : Int64) (target : Label)
    (here : fetch pc = some ⟨callInstruction target,5⟩) (kind : KcovKind)
    (contract : AllowedipsServiceReturns fetch (label target)
      (KcovReady kind) (KcovWrites kind) (KcovEffect kind))
    (c : CommonBitsCoverage.Context) (s : MachineData) (ready : CommonBitsCoverage.CallsReady c s)
    (rxSection : Nat)
    (silent : ∀ after, AllowedipsObservation.edge rxSection ⟨s,pc⟩ after = .ok [])
    (ordinary : pc ≠ Image.PeerGet.entry+0xaf ∧ pc ≠ Image.PeerGet.entry+0x4a) :
    Eventually (historyStep fetch) (fun t =>
      (Returned (calledState s (pc+5) (label target)) t.machine (pc+5).toUInt64 ∧
        CommonBitsCoverage.CallsReady c t.machine.data) ∧
      Local (fun a => InRange (s.regs.rsp.toBitVec-8) 8 a ∨ c.writes a)
        ⟨s,pc⟩ rxSection [] t)
      ⟨⟨s,pc⟩,[⟨s,pc⟩]⟩ := by
  have executed := CommonBitsCoverage.call fetch pc target here kind contract c s [⟨s,pc⟩] ready
  have withLast := history_last fetch _ _ rfl executed
  apply eventually_weaken (historyStep fetch) _ _ _ _ withLast
  rintro t ⟨⟨returned,nextReady,frame,tail,recorded,noOld,noNew⟩,last⟩
  refine ⟨⟨returned,nextReady⟩, ?_⟩
  refine ⟨by rw [recorded]; rfl, last, ?_, frame, ?_, ?_⟩
  · refine ⟨[], ?_, rfl⟩
    rw [recorded]
    have service := AllowedipsLoop.service_observation rxSection tail noOld noNew
    cases tail with
    | nil => rfl
    | cons called rest =>
      change (do
        let first ← AllowedipsObservation.edge rxSection ⟨s,pc⟩ called
        let later ← observeHistory (AllowedipsObservation.edge rxSection) (called::rest)
        pure (first++later)) = .ok []
      rw [silent,service]
      rfl
  · intro q member atCut
    rw [recorded] at member
    simp only [List.singleton_append, List.mem_cons] at member
    rcases member with first | inside
    · subst q; intro _ _; rfl
    · have nonempty : tail ≠ [] := List.ne_nil_of_mem inside
      have tailLast : tail.getLast? = some t.machine := by
        simpa only [recorded,List.singleton_append,List.getLast?_cons_of_ne_nil nonempty] using last
      rw [← AllowedipsLoop.history_restore tailLast] at inside
      rcases List.mem_append.mp inside with interior | endpoint
      · have outside := noNew q interior
        have mapped := cut_decoded q.pc atCut
        rw [outside] at mapped
        cases mapped
      · have same := List.mem_singleton.mp endpoint
        simpa only [same] using frame
  · intro q member
    rw [recorded] at member
    cases tail with
    | nil => simp at member
    | cons called rest =>
      simp only [List.singleton_append,List.dropLast_cons_cons,List.mem_cons] at member
      rcases member with first | interior
      · subst q; exact ordinary
      · have outside := noOld q interior
        constructor <;> intro equal <;> rw [equal] at outside <;> cases outside

end Binary.CommonBits
