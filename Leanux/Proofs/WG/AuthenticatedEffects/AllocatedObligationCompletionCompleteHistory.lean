import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionWorkerContract
import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalCompleteConverse

/-! Terminal-demand frames for exact completion prefixes. Birth quietness
alone is not used to preserve receipt completeness. The actual access
sub-observer emits only disposition events, and cannot hide a socket receipt. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete

theorem ledger_quiet (event : CausalJournal.Event) (quiet : ledgerEvent? event = none) : Quiet event := by
  cases event <;> try simp_all [ledgerEvent?,changesLedger]
  all_goals try (intro position; rfl)
  rename_i old
  cases old <;> simp_all
  intro position
  rfl

theorem extension (before : Complete history ledger) (grown : last = history ++ suffix)
    (quiet : last.filterMap ledgerEvent? = history.filterMap ledgerEvent?) : Complete last ledger := by
  have empty : suffix.filterMap ledgerEvent? = [] := by
    rw [grown,List.filterMap_append] at quiet
    exact List.append_cancel_left (as := history.filterMap ledgerEvent?)
      (by simpa only [List.append_nil] using quiet)
  rw [grown]
  exact before.append_quiet (fun event member => ledger_quiet event
    (List.filterMap_eq_nil_iff.mp empty event member))

theorem history_preserved (before : Complete history ledger) (appends : Appends action)
    (quiet : HistoryFrame ledgerEvent? action) : Complete (runPrefix action w history).2 ledger := by
  obtain ⟨suffix,grown⟩ := appends w history
  exact extension before grown (quiet w history)

theorem completion_events_quiet {events : List Completion.Event} (empty : events.filterMap Completion.socket? = []) :
    ∀ event ∈ events.map FirstTerminal.encode, Quiet event := by
  intro event member
  obtain ⟨original,inside,rfl⟩ := List.mem_map.mp member
  have none := List.filterMap_eq_nil_iff.mp empty original inside
  cases original with
  | disposition value => intro position; rfl
  | socket receipt => cases none

theorem access_no_socket (action : MixedM α) : HistoryFrame Completion.socket? (Completion.access action) :=
  focusPrefix_other _ _ _ (fun _ => rfl) _

theorem socket_body_no_socket (pid : PeerId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (ipv4 : Bool) :
    HistoryFrame Completion.socket? (CompletionFirstTerminal.socketBody pid packet peer ipv4) := by
  cases ipv4 <;> exact access_no_socket _

theorem no_socket_suffix (quiet : HistoryFrame Completion.socket? action)
    (performed : runPrefix action w history = (result,history ++ events)) :
    events.filterMap Completion.socket? = [] := by
  have unchanged := quiet w history
  rw [performed,List.filterMap_append] at unchanged
  exact List.append_cancel_left (as := history.filterMap Completion.socket?)
    (by simpa only [List.append_nil] using unchanged)

theorem settle_singleton (before : StagedEntry.Inv history ledger debts locals w)
    (complete : Complete history ledger)
    (pending : (ticket,Status.pending place) ∈ ledger)
    (selected : demand history.length event = some ⟨outcome,1⟩) :
    Complete (history ++ [event]) (settle [ticket] outcome ledger) := by
  apply complete.settle_cut (requested := ⟨outcome,1⟩) (chosen := [ticket])
    before.core.valid before.justified (by simp)
  · intro t member
    cases List.mem_singleton.mp member
    exact ⟨place,pending⟩
  · exact selected
  · rfl

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse
