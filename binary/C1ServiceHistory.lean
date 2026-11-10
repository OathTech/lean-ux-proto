import StatementC1Vacuity
import FiniteExecution

/-! Result C1, work package 4: from `Eventually` to an actual finite history.
The headline's steps conclude `Eventually (instructionStep fetch) post s`;
`Witness` asks for `Ran`, an actual history ending in a returned state. Every
such derivation contains one: follow any successor at each instruction. -/
namespace Binary.Statements.C1.Proof
open Binary.TrustBase Binary.Statements.C1
local instance : Labels := Image.linkedLabels

private theorem effects_end (effects : Effects) (post : MachineState → Prop)
    (run : effects.All post) : ∃ t, post t := by
  induction effects with
  | done s => exact ⟨s,run⟩
  | unimplemented _ => exact False.elim run
  | gp_unaligned _ _ => exact False.elim run
  | nonmem_load => exact False.elim run
  | nonmem_store => exact False.elim run
  | undefined next ih => exact ih (NondetSupportingType.from_hash 0) (run _)
  | require_read_access _ _ next ih | require_write_access _ _ next ih | require_exec_access _ next ih =>
    exact ih () run

/-- An executed instruction has a successor. -/
theorem instruction_ends {fetch : Int64 → Option Decoded} {post : MachineState → Prop}
    {s : MachineState} (step : instructionStep fetch s post) : ∃ t, post t := by
  unfold instructionStep at step
  cases read : fetch s.pc with
  | none => simp only [read] at step
  | some decoded =>
    simp only [read] at step
    exact effects_end _ _ step.2

/-- A derivation ends somewhere. -/
theorem eventually_ends {fetch : Int64 → Option Decoded} {post : MachineState → Prop}
    {s : MachineState} (run : Eventually (instructionStep fetch) post s) : ∃ t, post t := by
  induction run with
  | done s hp => exact ⟨s,hp⟩
  | step s mid step _ ih =>
    obtain ⟨next,reached⟩ := instruction_ends step
    exact ih next reached

/-- A derivation extends any actual history that ends at its start to one
that ends where the postcondition holds. -/
theorem eventually_history {fetch : Int64 → Option Decoded} {post : MachineState → Prop}
    {s : MachineState} (run : Eventually (instructionStep fetch) post s) :
    ∀ (initial : MachineState) (history : List MachineState), ActualHistory fetch initial history →
      history.getLast? = some s →
      ∃ t final, ActualHistory fetch initial final ∧ final.getLast? = some t ∧ post t := by
  induction run with
  | done s hp => exact fun initial history actual last => ⟨s,history,actual,last,hp⟩
  | step s mid step _ ih =>
    intro initial history actual last
    obtain ⟨next,successor,reached⟩ := instruction_ends (instruction_successors fetch s mid step)
    exact ih next reached initial (history ++ [next]) (.snoc actual last successor) (by simp)

/-- `Ran` from a step of the headline: a derivation whose postcondition
includes the return gives an actual history to a returned state. -/
theorem ran_of_eventually {fetch : Int64 → Option Decoded} {post : MachineState → Prop}
    {s : MachineState} {ra : UInt64} (run : Eventually (instructionStep fetch) post s)
    (returns : ∀ t, post t → Returned s t ra) :
    ∃ t history, Ran fetch s t ra history ∧ post t := by
  obtain ⟨t,history,actual,last,reached⟩ := eventually_history run s [s] .start rfl
  exact ⟨t,history,⟨actual,last,returns t reached⟩,reached⟩

#print axioms ran_of_eventually
end Binary.Statements.C1.Proof
