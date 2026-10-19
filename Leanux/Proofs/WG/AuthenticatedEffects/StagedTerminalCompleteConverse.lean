import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalCompleteSettlement
import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalCompleteFrames

/-! Consequences of the explicit converse companion. Singleton data socket,
unsupported-family and labelled-drop receipts identify exactly one terminal
ticket; fixed ledger uniqueness then excludes two receipt positions for the
same ticket. Initialized source transport is still separate. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalComplete
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open CausalJournal StagedProvenance

/-- An actual singleton terminal receipt is accounted by exactly one fixed
ticket, provided the same ledger's historical converse has been transported. -/
theorem Complete.singleton (before : Complete history ledger)
    (selected : history[position]? = some event)
    (requested : demand position event = some ⟨outcome,1⟩) :
    ∃ ticket, (ticket,Status.terminal outcome) ∈ ledger ∧
      ∀ other, (other,Status.terminal outcome) ∈ ledger → other = ticket := by
  have count := before.at selected ⟨outcome,1⟩ requested
  obtain ⟨ticket,same⟩ := List.length_eq_one_iff.mp count
  refine ⟨ticket,?_,?_⟩
  · apply mem_tickets.mp
    rw [same]
    exact List.mem_cons_self ..
  · intro other member
    have inside := mem_tickets.mpr member
    rw [same] at inside
    exact List.mem_singleton.mp inside

theorem Complete.socket (before : Complete history ledger)
    (selected : history[position]? = some (.old (.socket receipt))) :
    ∃ ticket, (ticket,Status.terminal (.socket position (receipt.socket.value == 0))) ∈ ledger ∧
      ∀ other, (other,Status.terminal (.socket position (receipt.socket.value == 0))) ∈ ledger → other = ticket :=
  before.singleton selected rfl

theorem Complete.labelled_drop (before : Complete history ledger)
    (selected : history[position]? = some (.terminalDrop receipt)) :
    ∃ ticket, (ticket,Status.terminal (.disposed position receipt.reason)) ∈ ledger ∧
      ∀ other, (other,Status.terminal (.disposed position receipt.reason)) ∈ ledger → other = ticket :=
  before.singleton selected rfl

theorem Complete.unsupported (before : Complete history ledger)
    (selected : history[position]? = some (.sendResult receipt))
    (unsupported : ¬(endpointFamily receipt.run.before.wg receipt.pid = AF_INET ∨
      endpointFamily receipt.run.before.wg receipt.pid = AF_INET6)) :
    ∃ ticket, (ticket,Status.terminal (.sendRefused position)) ∈ ledger ∧
      ∀ other, (other,Status.terminal (.sendRefused position)) ∈ ledger → other = ticket :=
  before.singleton selected (unsupported_result_demand unsupported)

/-- A fixed ticket cannot discharge terminal demands at two distinct receipt
positions. The ledger's key uniqueness and the exact stored outcomes supply
the exclusion; an existential ledger chosen separately for each receipt does
not supply this result. -/
theorem one_position (valid : Valid domain ledger)
    (left : (ticket,Status.terminal first) ∈ ledger)
    (right : (ticket,Status.terminal second) ∈ ledger) :
    terminalPosition first = terminalPosition second := by
  exact congrArg terminalPosition (Status.terminal.inj
    (unique_status (valid.1.symm ▸ valid.2) left right))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalComplete
