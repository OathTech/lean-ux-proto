import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePassive
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntrySourceQuiet

/-! A terminal history frame is separate from a native endpoint frame and
from birth quietness. Together they retain the same complete ledger on every
passive prefix, including a native Stop without a returned final world. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteQuiet
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open CompleteCarrier StagedTerminalComplete

noncomputable def terminal? (event : Event) : Option Event := by
  classical
  exact if Quiet event then none else some event

theorem terminal_none (quiet : Quiet event) : terminal? event = none := by
  simp only [terminal?,quiet,ite_true]

theorem suffix {body : WGPrefix Event α} (appends : StateAppends body)
    (frame : StateHistoryFrame terminal? body) (w : WGWorld) (a : Ambient) (h : List Event) :
    ∃ suffix, (runWGPrefix body w a h).2 = h ++ suffix ∧ ∀ event ∈ suffix, Quiet event := by
  obtain ⟨suffix,grown⟩ := appends w a h
  have filtered := frame w a h
  change (runWGPrefix body w a h).2.filterMap terminal? = h.filterMap terminal? at filtered
  change (runWGPrefix body w a h).2 = h ++ suffix at grown
  rw [grown,List.filterMap_append] at filtered
  have empty : suffix.filterMap terminal? = [] :=
    List.append_cancel_left (as := h.filterMap terminal?) (by simpa only [List.append_nil] using filtered)
  refine ⟨suffix,grown,?_⟩
  intro event member
  have absent := List.filterMap_eq_nil_iff.mp empty event member
  classical
  by_cases quiet : Quiet event
  · exact quiet
  · simp only [terminal?,quiet,ite_false] at absent
    cases absent

theorem passive {body : WGPrefix Event α} (checked : Passive.Checked ledger debts locals body)
    (appends : StateAppends body) (frame : StateHistoryFrame terminal? body) :
    CompleteCarrier.Checked ledger debts locals body :=
  CompleteCarrier.passive body checked (suffix appends frame)

theorem native_fixed {body : WGPrefix Event α} {native : WG.M α}
    (erases : ErasesStatePrefix body native) (appends : StateAppends body)
    (births : StateHistoryFrame SourceQuiet.birth? body) (terminals : StateHistoryFrame terminal? body)
    (frame : SameView StagedEntry.view native) : CompleteCarrier.Checked ledger debts locals body := by
  intro w a h before
  obtain ⟨events,grown,birthFree⟩ := SourceQuiet.quiet_suffix appends births w a h
  obtain ⟨other,extended,terminalFree⟩ := suffix appends terminals w a h
  have same : events = other := List.append_cancel_left (grown.symm.trans extended)
  subst other
  have atHistory := before.append_quiet events birthFree terminalFree
  change (runPrefix (body.run w) a h).2 = h ++ events at grown
  refine ⟨events,grown,?_,?_⟩
  · rw [grown]
    exact ⟨w,atHistory⟩
  · cases performed : (runPrefix (body.run w) a h).1 with
    | error stop => trivial
    | ok out =>
      obtain ⟨⟨value,v⟩,b⟩ := out
      have run := erases w a h
      change (runPrefix (body.run w) a h).1 = _ at run
      rw [performed] at run
      have view := (ProjectedAction.iff_run_ambient _ _ _).mp frame w a value v b run.symm
      change Accounted (runPrefix (body.run w) a h).2 ledger debts locals v
      rw [grown]
      exact atHistory.same_view view

theorem checked (Safe : List Event → Prop)
    (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h)
    {body : WGPrefix Event α} {native : WG.M α}
    (erases : ErasesStatePrefix body native) (appends : StateAppends body)
    (births : StateHistoryFrame SourceQuiet.birth? body) (terminals : StateHistoryFrame terminal? body)
    (frame : SameView StagedEntry.view native) : CompletePassive.Checked debts locals Safe body :=
  CompletePassive.fixed Safe accountSafe (fun _ => native_fixed erases appends births terminals frame)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteQuiet
