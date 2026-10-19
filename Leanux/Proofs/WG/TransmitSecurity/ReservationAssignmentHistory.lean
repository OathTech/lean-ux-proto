import Leanux.Proofs.WG.TransmitSecurity.ReservationAssignments

/-! Prefix safety for injective positional reservation credits. An open batch's
credits persist only across events outside the allocation family. -/
namespace Leanux.Proofs.WG.TransmitSecurity.ReservationAssignments
open Leanux Leanux.WG Leanux.Proofs.Logged

def QuietMonotone (P : List Journal.Event → Prop) : Prop :=
  ∀ h suffix, (∀ event ∈ suffix, ReservationHistory.allocation? event = none) → P h → P (h ++ suffix)

def Keep (P : List Journal.Event → Prop) (h : List Journal.Event) (_ : WGWorld) (_ : Ambient) : Prop :=
  Safe h ∧ P h

theorem Safe.append (old : Safe h)
    (new : ∀ pre event post, suffix = pre ++ event :: post → Checked (h ++ pre) event) : Safe (h ++ suffix) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.HistorySupport.«0».Leanux.Proofs.WG.Origins.HistorySupport.positions_append)
    Checked h suffix old new

theorem Safe.quiet (old : Safe h) (quiet : ReservationHistory.allocation? event = none) : Safe (h ++ [event]) := by
  apply old.append
  intro pre e post position
  have member : e ∈ [event] := by rw [position]; simp
  have same := List.mem_singleton.mp member
  subst e
  cases event <;> simp_all only [ReservationHistory.allocation?,Checked,reduceCtorEq]

theorem Safe.quiet_suffix (old : Safe h) (quiet : suffix.filterMap ReservationHistory.allocation? = []) : Safe (h ++ suffix) := by
  apply old.append
  intro pre event post position
  cases event <;> simp only [Checked]
  rename_i packets run
  have member : Journal.Event.allocated packets run ∈ suffix := by rw [position]; simp
  have found : (packets,run) ∈ suffix.filterMap ReservationHistory.allocation? := List.mem_filterMap.mpr ⟨_,member,rfl⟩
  rw [quiet] at found
  cases found

theorem empty : Safe [] := by intro pre event post position; cases pre <;> cases position

theorem quiet {g : WGPrefix Journal.Event α} (appends : StateAppends g)
    (quiet : StateHistoryFrame ReservationHistory.allocation? g) (mono : QuietMonotone P) :
    StatePrefixPreserves (Keep P) Safe g := by
  intro w a h hi
  obtain ⟨suffix,equal⟩ := appends w a h
  have excluded : suffix.filterMap ReservationHistory.allocation? = [] := by
    have same := quiet w a h
    rw [equal,List.filterMap_append] at same
    have lengths := congrArg List.length same
    cases found : suffix.filterMap ReservationHistory.allocation? with
    | nil => rfl
    | cons e es =>
      simp only [List.length_append,found,List.length_cons] at lengths
      omega
  have safe : Safe (runPrefix (g.run w) a h).2 := by rw [equal]; exact hi.1.quiet_suffix excluded
  refine ⟨suffix,equal,safe,?_⟩
  cases run : (runPrefix (g.run w) a h).1 with
  | error stop => trivial
  | ok out =>
    refine ⟨safe,?_⟩
    rw [equal]
    apply mono h suffix _ hi.2
    intro event member
    cases found : ReservationHistory.allocation? event with
    | none => rfl
    | some allocation =>
      have included := List.mem_filterMap.mpr ⟨event,member,found⟩
      rw [excluded] at included
      cases included

theorem lift (action : WG.M α) : StatePrefixPreserves (Keep P) Safe (liftWGPrefix action) :=
  StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1) (fun _ _ _ _ _ _ hi _ => hi)

theorem pure (value : α) : StatePrefixPreserves (Keep P) Safe (Pure.pure value) :=
  StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.1) (fun _ _ _ hi => hi)

end Leanux.Proofs.WG.TransmitSecurity.ReservationAssignments
