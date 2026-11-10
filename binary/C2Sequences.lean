import C2CutInterfaces
import FiniteExecution
import HistoryGuard

/-! Work package 3 of result C2: representation, the mirror link, first exits and the
witness (`WindowMapped` to `WitnessStart` of `C2CutInterfaces`). Brief:
packets/c2/proof/WP3.md.

One file: the lakefile lists every module of the package as a root and is not edited by
a work package, so a module imported from this root that is not itself a root cannot be
built; the sections below would otherwise be files of their own. -/

/-! Work package 3 of result C2, first exits: an `Eventually` proof that every execution
from `s` reaches an exit first with `P` against an actual first exit
(`FirstExitDetermined`, `FirstExitExists`). -/
namespace Binary.C2
open Binary TrustBase Leanux
local instance : Labels := Binary.Image.linkedLabels

/-- A proved instruction step holds of each actual successor. -/
theorem effects_successor (effects : Effects) (post : MachineState → Prop)
    (run : effects.All post) (t : MachineState) (next : EffectSuccessor effects t) : post t := by
  induction effects with
  | done s => exact next ▸ run
  | unimplemented _ => exact False.elim run
  | gp_unaligned _ _ => exact False.elim run
  | nonmem_load => exact False.elim run
  | nonmem_store => exact False.elim run
  | undefined continuation ih =>
    obtain ⟨value, rest⟩ := next
    exact ih value (run value) rest
  | require_read_access _ _ continuation ih | require_write_access _ _ continuation ih
  | require_exec_access _ continuation ih =>
    exact ih () run next

theorem instruction_successor (fetch : Int64 → Option Decoded) (s t : MachineState)
    (post : MachineState → Prop) (run : instructionStep fetch s post)
    (next : InstructionSuccessor fetch s t) : post t := by
  obtain ⟨decoded, fetched, _, successor⟩ := next
  unfold instructionStep at run
  simp only [fetched] at run
  exact effects_successor _ post run.2 t successor

/-- An actual history that continues past a prefix continues it by an actual successor
of the prefix's last state. -/
theorem actual_successor {fetch : Int64 → Option Decoded} {s : MachineState}
    {history : List MachineState} (actual : ActualHistory fetch s history) :
    ∀ (front : List MachineState) (current next : MachineState) (rest : List MachineState),
      history = front ++ next :: rest → front.getLast? = some current →
      InstructionSuccessor fetch current next := by
  induction actual with
  | start =>
    intro front current next rest equal last
    cases front with
    | nil => simp at last
    | cons a front => cases front <;> simp at equal
  | @snoc history current' next' prior last' successor ih =>
    intro front current next rest equal last
    rcases List.eq_nil_or_concat rest with rfl | ⟨rest', final, rfl⟩
    · have split : history = front ∧ next' = next := by
        have := List.append_inj' equal rfl
        exact ⟨this.1, by simpa using this.2⟩
      obtain ⟨rfl, rfl⟩ := split
      rw [last'] at last
      cases last
      exact successor
    · have equal' : history ++ [next'] = (front ++ next :: rest') ++ [final] := by
        simpa [List.concat_eq_append, List.append_assoc] using equal
      have := List.append_inj' equal' rfl
      exact ih front current next rest' this.1 last

/-- The induction behind `FirstExitDetermined`: a proof from an executed state whose
history is a prefix of an actual history ending at its first exit speaks of that exit. -/
theorem first_exit_of_prefix (fetch : Int64 → Option Decoded) (s t : MachineState)
    (P : MachineState → Prop) (whole : List MachineState)
    (actual : ActualHistory fetch s whole) (ends : whole.getLast? = some t)
    (exit : t.pc ∈ exits) (first : ∀ u ∈ whole.dropLast, u.pc ∉ exits)
    (e : Executed)
    (run : Eventually (historyStep fetch)
      (fun e => e.machine.pc ∈ exits ∧ (∀ u ∈ e.history.dropLast, u.pc ∉ exits) ∧ P e.machine) e) :
    e.history.getLast? = some e.machine → (∃ rest, whole = e.history ++ rest) → P t := by
  induction run with
  | done e post =>
    rintro last ⟨rest, equal⟩
    cases rest with
    | nil =>
      rw [List.append_nil] at equal
      rw [equal, last] at ends
      cases ends
      exact post.2.2
    | cons next rest =>
      exfalso
      obtain ⟨front, split⟩ := List.getLast?_eq_some_iff.mp last
      apply first e.machine _ post.1
      rw [equal, List.dropLast_append_of_ne_nil (by simp), split]
      simp
  | step e mid step branches ih =>
    rintro last ⟨rest, equal⟩
    cases rest with
    | nil =>
      exfalso
      rw [List.append_nil] at equal
      rw [equal, last] at ends
      cases ends
      obtain ⟨next, reached⟩ := Callback.instruction_witness step
      obtain ⟨leaf, post, tail, recorded⟩ := Callback.history_witness (branches _ reached)
      obtain ⟨front, split⟩ := List.getLast?_eq_some_iff.mp last
      apply post.2.1 e.machine _ exit
      rw [recorded]
      change e.machine ∈ ((e.history ++ [next]) ++ tail).dropLast
      rw [split]
      cases tail with
      | nil => simp
      | cons a tail =>
        rw [List.dropLast_append_of_ne_nil (by simp)]
        simp
    | cons next rest =>
      have successor := actual_successor actual e.history e.machine next rest equal last
      have reached := instruction_successor fetch e.machine next _ step successor
      exact ih _ reached (by simp) ⟨rest, by simpa using equal⟩

theorem first_exit_determined : FirstExitDetermined := by
  rintro fetch s t P run ⟨whole, actual, ends, exit, first⟩
  refine first_exit_of_prefix fetch s t P whole actual ends exit first ⟨s, [s]⟩ run rfl ?_
  have starts : ∀ {history}, ActualHistory fetch s history → ∃ rest, history = [s] ++ rest := by
    intro history h
    induction h with
    | start => exact ⟨[], rfl⟩
    | @snoc _ _ next _ _ _ ih =>
      obtain ⟨rest, equal⟩ := ih
      exact ⟨rest ++ [next], by rw [equal]; simp⟩
  exact starts actual

theorem first_exit_exists : FirstExitExists := by
  intro fetch s P run
  have traced := eventually_actual fetch s _ ⟨s, [s]⟩ run .start rfl
  have ended := history_last fetch _ ⟨s, [s]⟩ rfl traced
  obtain ⟨leaf, ⟨⟨⟨exit, first, holds⟩, actual⟩, last⟩, _⟩ := Callback.history_witness ended
  exact ⟨leaf.machine, ⟨leaf.history, actual, last, exit, first⟩, holds⟩

#print axioms first_exit_determined
#print axioms first_exit_exists
end Binary.C2
