import Kraken.X64.OmniSemantics

namespace Binary

theorem all_mono (e : Effects) (P Q : MachineState → Prop)
    (h : ∀ s, P s → Q s) : e.All P → e.All Q := by
  induction e with
  | done s => exact h s
  | unimplemented _ => exact False.elim
  | gp_unaligned _ _ => exact False.elim
  | nonmem_load => exact False.elim
  | nonmem_store => exact False.elim
  | undefined k ih => exact fun hp v => ih v (hp v)
  | require_read_access a w k ih => exact ih ()
  | require_write_access a w k ih => exact ih ()
  | require_exec_access p k ih => exact ih ()

/-- Actual linked addresses and lengths; never Kraken's fake layout. -/
structure Decoded where
  instruction : Instr
  size : Nat

/-- Reject a missing instruction. In particular, falling off a decoded range
    is not a return. Callee contracts use this same whole-image transition. -/
def instructionStep [Labels] (fetch : Int64 → Option Decoded)
    (s : MachineState) (post : MachineState → Prop) : Prop :=
  match fetch s.pc with
  | none => False
  | some i => i.size > 0 ∧
    (i.instruction.interp s.data ⟨s.pc, s.pc + .ofNat i.size⟩
      (fun d => .done ⟨d, s.pc + .ofNat i.size⟩)
      (fun p d => .done ⟨d, p⟩)).All post

/-- Transport is ordinary predicate implication after the execution theorem.
    A function-specific proof must establish `simulation` for its actual R;
    this lemma alone certifies no binary function or mirror property. -/
theorem transport {S W : Type} (step : S → (S → Prop) → Prop)
    (R : S → W → Prop) (accepted : W → Prop) (start : S)
    (simulation : Eventually step (fun t => ∃ w, accepted w ∧ R t w) start)
    (P : W → Prop) (property : ∀ w, accepted w → P w) :
    Eventually step (fun t => ∃ w, accepted w ∧ R t w ∧ P w) start := by
  apply eventually_weaken step _ _ start _ simulation
  rintro t ⟨w, hw, hr⟩
  exact ⟨w, hw, hr, property w hw⟩

#print axioms transport

end Binary
