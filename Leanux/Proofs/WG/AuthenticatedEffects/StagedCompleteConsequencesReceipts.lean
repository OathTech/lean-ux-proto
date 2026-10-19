import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteConsequencesPartition

/-! Every actual terminal demand has its exact number of fixed tickets in
one ledger. Socket errno and unsupported-family refusal remain distinct; an
ordinary later free carries cleanup debt and creates no terminal demand. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteConsequences
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open RetirementSecurity AllocatedObligation CausalJournal StagedProvenance StagedTerminalComplete

private theorem terminal_tickets_sublist (outcome : Staged.Obligations.Terminal) (ledger : Ledger) :
    List.Sublist (tickets outcome ledger) (keys ledger) := by
  classical
  induction ledger with
  | nil => exact .slnil
  | cons entry tail ih =>
    obtain ⟨ticket,status⟩ := entry
    cases status with
    | pending location => simpa [tickets,keys] using List.Sublist.cons ticket ih
    | terminal actual =>
      by_cases same : actual=outcome
      · simpa [tickets,keys,same] using List.Sublist.cons_cons ticket ih
      · simpa [tickets,keys,same] using List.Sublist.cons ticket ih

theorem Cut.terminal_domain (cut : Cut history ledger debts locals w)
    (member : (ticket,Status.terminal outcome) ∈ ledger) : ticket ∈ births history := by
  rw [←cut.core.valid.1]
  exact List.mem_map.mpr ⟨_,member,rfl⟩

/-- Every historical terminal receipt has precisely its native arity of
actual birth tickets, with valid strict-prefix source evidence for each. -/
theorem Cut.converse (cut : Cut history ledger debts locals w)
    (atPosition : history[position]? = some event)
    (requested : demand position event = some request) :
    (tickets request.outcome ledger).Nodup ∧
      (tickets request.outcome ledger).length = request.count ∧
      ∀ ticket ∈ tickets request.outcome ledger,
        ticket ∈ births history ∧ Evidence history ticket request.outcome := by
  refine ⟨(terminal_tickets_sublist request.outcome ledger).nodup
    (cut.core.valid.1.symm ▸ cut.core.valid.2),cut.complete.at atPosition request requested,?_⟩
  intro ticket member
  have terminal := mem_tickets.mp member
  exact ⟨cut.terminal_domain terminal,cut.justified ticket request.outcome terminal⟩

/-- A single socket or counterless disposal receipt has one and only one
admitted ticket in the complete account, including a failed socket call. -/
theorem Cut.singleton (cut : Cut history ledger debts locals w)
    (atPosition : history[position]? = some event)
    (requested : demand position event = some ⟨outcome,1⟩) :
    ∃ ticket, ticket ∈ births history ∧ (ticket,Status.terminal outcome) ∈ ledger ∧
      Evidence history ticket outcome ∧
      ∀ other, (other,Status.terminal outcome) ∈ ledger → other=ticket := by
  obtain ⟨ticket,member,unique⟩ := cut.complete.singleton atPosition requested
  exact ⟨ticket,cut.terminal_domain member,member,cut.justified ticket outcome member,unique⟩

theorem Cut.socket (cut : Cut history ledger debts locals w)
    (atPosition : history[position]? = some (.old (.socket receipt))) :
    ∃ ticket, ticket ∈ births history ∧
      (ticket,Status.terminal (.socket position (receipt.socket.value == 0))) ∈ ledger ∧
      Evidence history ticket (.socket position (receipt.socket.value == 0)) ∧
      ∀ other, (other,Status.terminal (.socket position (receipt.socket.value == 0))) ∈ ledger → other=ticket :=
  cut.singleton atPosition rfl

theorem Cut.labelled_drop (cut : Cut history ledger debts locals w)
    (atPosition : history[position]? = some (.terminalDrop receipt)) :
    ∃ ticket, ticket ∈ births history ∧
      (ticket,Status.terminal (.disposed position receipt.reason)) ∈ ledger ∧
      Evidence history ticket (.disposed position receipt.reason) ∧
      ∀ other, (other,Status.terminal (.disposed position receipt.reason)) ∈ ledger → other=ticket :=
  cut.singleton atPosition rfl

theorem Cut.unsupported (cut : Cut history ledger debts locals w)
    (atPosition : history[position]? = some (.sendResult receipt))
    (unsupported : ¬(endpointFamily receipt.run.before.wg receipt.pid = AF_INET ∨
      endpointFamily receipt.run.before.wg receipt.pid = AF_INET6)) :
    ∃ ticket, ticket ∈ births history ∧ (ticket,Status.terminal (.sendRefused position)) ∈ ledger ∧
      Evidence history ticket (.sendRefused position) ∧
      ∀ other, (other,Status.terminal (.sendRefused position)) ∈ ledger → other=ticket :=
  cut.singleton atPosition (unsupported_result_demand unsupported)

/-- The global safety premise yields both accounting directions on the SAME
ledger, with explicit native pending ownership even at selected Stop cuts. -/
theorem conservation (safe : CompleteProduct.Safe history) :
    ∃ ledger debts locals w, Cut history ledger debts locals w ∧
      (∀ ticket ∈ births history, ∃ status, (ticket,status) ∈ ledger ∧
        StatusEvidence history ledger locals w ticket status ∧
        ∀ other, (ticket,other) ∈ ledger → other=status) ∧
      (∀ position event request, history[position]? = some event →
        demand position event = some request →
        (tickets request.outcome ledger).Nodup ∧
          (tickets request.outcome ledger).length = request.count ∧
          ∀ ticket ∈ tickets request.outcome ledger,
            ticket ∈ births history ∧ Evidence history ticket request.outcome) := by
  obtain ⟨ledger,debts,locals,w,cut⟩ := safe_cut safe
  exact ⟨ledger,debts,locals,w,cut,fun _ born=>cut.partition born,
    fun _ _ _ atPosition request=>cut.converse atPosition request⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteConsequences
