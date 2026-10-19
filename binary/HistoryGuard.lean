import StackGuard

namespace Binary.Callback
local instance : Labels := Image.linkedLabels

/-- Retain the ordinary complete history while restricting each executed
instruction's starting state. -/
def guardedHistoryStep (fetch : Int64 → Option Decoded) (guard : MachineState → Prop)
    (s : Executed) (post : Executed → Prop) : Prop :=
  guard s.machine ∧ historyStep fetch s post

theorem all_witness {effects : Effects} {P : MachineState → Prop}
    (run : effects.All P) : ∃ s, P s := by
  induction effects with
  | done s => exact ⟨s,run⟩
  | unimplemented _ => exact False.elim run
  | gp_unaligned _ _ => exact False.elim run
  | nonmem_load => exact False.elim run
  | nonmem_store => exact False.elim run
  | undefined next ih => exact ih (NondetSupportingType.from_hash 0) (run _)
  | require_read_access _ _ next ih | require_write_access _ _ next ih | require_exec_access _ next ih =>
    exact ih () run

theorem instruction_witness {fetch s P} (run : instructionStep fetch s P) : ∃ t, P t := by
  unfold instructionStep at run
  split at run
  · contradiction
  · exact all_witness run.2

/-- Existence here follows from a universally terminating proof. It is used
only to establish the guard at the root; all execution branches are retained. -/
theorem history_witness {fetch s P} (run : Eventually (historyStep fetch) P s) :
    ∃ t, P t ∧ ∃ tail, t.history=s.history++tail := by
  induction run with
  | done s hp => exact ⟨s,hp,[],by simp⟩
  | step s mid step _ ih =>
    obtain ⟨next,hn⟩ := instruction_witness step
    obtain ⟨t,hp,tail,equal⟩ := ih ⟨next,s.history++[next]⟩ hn
    exact ⟨t,hp,next::tail,by simpa only [List.append_assoc,List.singleton_append] using equal⟩

/-- Recover an interior guard already established for a complete recorded
region. This reuses its universal execution proof, not a tested trace.
The prefix before `front.length` is outside this local obligation. -/
theorem history_guard {fetch s P guard}
    (run : Eventually (historyStep fetch) P s) :
    ∀ front, s.history=front++[s.machine] →
      (∀ t, P t → ∀ q ∈ t.history.dropLast.drop front.length, guard q) →
      Eventually (guardedHistoryStep fetch guard) P s := by
  induction run with
  | done s hp => intros; exact .done s hp
  | step s mid step branches ih =>
    intro front last safe
    obtain ⟨next,hn⟩ := instruction_witness step
    obtain ⟨final,hfinal,tail,recorded⟩ := history_witness (branches ⟨next,s.history++[next]⟩ hn)
    have current : guard s.machine := by
      apply safe final hfinal
      rw [recorded,last]
      cases tail with
      | nil => simp
      | cons a tail => simp [List.append_assoc,List.dropLast_append_of_ne_nil]
    apply step_cps
    refine ⟨current,?_⟩
    apply instruction_mono fetch s.machine _ _ _ step
    intro next hn
    apply ih ⟨next,s.history++[next]⟩ hn (front++[s.machine])
    · simp only [last,List.append_assoc]
    · intro t hp q member
      apply safe t hp q
      have small : q ∈ (t.history.dropLast.drop front.length).drop 1 := by
        simpa only [List.drop_drop,List.length_append,List.length_singleton] using member
      exact List.mem_of_mem_drop small

theorem guarded_history_project {fetch guard s P}
    (run : Eventually (guardedHistoryStep fetch guard) P s) :
    Eventually (guardedStep fetch guard) (fun t => ∃ history, P ⟨t,history⟩) s.machine := by
  induction run with
  | done s hp => exact .done _ ⟨s.history,hp⟩
  | step s mid step _ ih =>
    apply step_cps
    exact ⟨step.1,instruction_mono fetch s.machine _ _ (fun t h => ih ⟨t,s.history++[t]⟩ h) step.2⟩

/-- A fixed region often already exports its exact successor list. Use that
list to recover its guard without repeating the instruction calculations. -/
theorem history_guard_suffix {fetch s P guard}
    (run : Eventually (historyStep fetch) P s)
    (last : s.history.getLast?=some s.machine)
    (safe : ∀ t, P t → ∃ suffix, t.history=s.history++suffix ∧
      ∀ q ∈ (s.machine::suffix).dropLast, guard q) :
    Eventually (guardedHistoryStep fetch guard) P s := by
  apply history_guard run s.history.dropLast (history_restore last).symm
  intro t hp q member
  obtain ⟨suffix,recorded,guarded⟩ := safe t hp
  apply guarded q
  have shape : t.history=s.history.dropLast++(s.machine::suffix) := by
    calc
      t.history = s.history++suffix := recorded
      _ = (s.history.dropLast++[s.machine])++suffix := by rw [history_restore last]
      _ = _ := by simp only [List.append_assoc,List.singleton_append]
  rw [shape,List.dropLast_append_of_ne_nil (by simp : s.machine::suffix≠[])] at member
  simpa only [List.drop_append,List.drop_length,List.nil_append,Nat.sub_self,List.drop_zero] using member

/-- A guarded execution still records every instruction successor. -/
theorem guarded_to_history {fetch guard s P}
    (run : Eventually (guardedHistoryStep fetch guard) P s) :
    Eventually (historyStep fetch) P s := by
  induction run with
  | done s hp => exact .done _ hp
  | step s mid step _ ih =>
    apply step_cps
    exact instruction_mono fetch s.machine _ _ (fun t h => ih ⟨t,s.history++[t]⟩ h) step.2

#print axioms history_guard
#print axioms guarded_history_project
end Binary.Callback
