import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixPassive
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteSourceQuiet

/-! Separate birth and terminal history frames certify every appended cut.
The native endpoint frame remains necessary for the normal successor carrier;
it is not used to reconstruct a state inside a stopped computation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.QuietSource
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open TransmitSecurity CausalJournal

theorem checked (Safe : List Event→Prop)
    (accountSafe : ∀ ledger h w, CompleteCarrier.Accounted h ledger debts locals w→Safe h)
    {body : WGPrefix Event α} {native : WG.M α}
    (erases : ErasesStatePrefix body native) (appends : StateAppends body)
    (births : StateHistoryFrame SourceQuiet.birth? body)
    (terminals : StateHistoryFrame CompleteQuiet.terminal? body)
    (frame : SameView StagedEntry.view native) : Passive.Checked debts locals Safe body := by
  apply StateEnsures.of_cuts (CompleteQuiet.checked Safe accountSafe erases appends births terminals frame)
  intro w a h before
  obtain ⟨ledger,accounted⟩ := before
  obtain ⟨events,grown,birthFree⟩ := SourceQuiet.quiet_suffix appends births w a h
  obtain ⟨other,extended,terminalFree⟩ := CompleteQuiet.suffix appends terminals w a h
  have same : events=other := List.append_cancel_left (grown.symm.trans extended)
  subst other
  refine ⟨events,grown,?_⟩
  intro n _
  exact accountSafe ledger _ w (accounted.append_quiet (events.take n)
    (fun event member=>birthFree event (List.mem_of_mem_take member))
    (fun event member=>terminalFree event (List.mem_of_mem_take member)))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.QuietSource
