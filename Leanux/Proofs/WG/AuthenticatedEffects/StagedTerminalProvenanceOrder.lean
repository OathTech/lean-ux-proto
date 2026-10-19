import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalAllocatedCuts

/-! Terminal provenance refers to an actual strict-later event than the
ticket's birth. This consequence distinguishes labels at arbitrary positions
from receipt-backed dispositions; initialized completeness is still separate. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedProvenance
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open CausalJournal

def terminalPosition : Staged.Obligations.Terminal → Nat
  | .counted position _ => position
  | .socket position _ => position
  | .sendRefused position => position
  | .disposed position _ => position

theorem At.position (evidence : At history event ticket outcome) :
    terminalPosition outcome = history.length := by
  cases evidence <;> rfl

theorem At.born (evidence : At history event ticket outcome) :
    ∃ generation pid stamp packet, Born history generation pid stamp ticket packet := by
  cases evidence with
  | overflow pid r native part generation epoch tickets aligned member =>
    obtain ⟨packet,born⟩ := aligned.ticket_member (List.mem_of_mem_take member)
    exact ⟨generation,pid,part.stamp,packet,born⟩
  | purge pid r native part whole generation epoch tickets aligned member =>
    obtain ⟨packet,born⟩ := aligned.ticket_member member
    exact ⟨generation,pid,part.stamp,packet,born⟩
  | released peer r native pid p result generation epoch tickets aligned member =>
    obtain ⟨packet,born⟩ := aligned.ticket_member member
    exact ⟨generation,pid,p.internalId,packet,born⟩
  | socket r native batch ordinal generation material lineage backed =>
    obtain ⟨_,pid,stamp,born,_⟩ := lineage
    exact ⟨generation,pid,stamp,material.plaintext,born⟩
  | refused r native failed peer read entry not4 not6 batch ordinal generation material lineage backed =>
    obtain ⟨_,pid,stamp,born,_⟩ := lineage
    exact ⟨generation,pid,stamp,material.plaintext,born⟩
  | disposed r native batch ordinal generation material lineage backed =>
    obtain ⟨_,pid,stamp,born,_⟩ := lineage
    exact ⟨generation,pid,stamp,material.plaintext,born⟩

theorem Evidence.order (evidence : Evidence history ticket outcome) :
    ticket.position < terminalPosition outcome ∧ terminalPosition outcome < history.length := by
  obtain ⟨before,event,after,rfl,atCut⟩ := evidence
  obtain ⟨_,_,_,_,born⟩ := atCut.born
  rw [atCut.position]
  exact ⟨born.position_lt,by simp⟩

theorem Justified.order (before : Justified history ledger)
    (terminal : (ticket,Status.terminal outcome) ∈ ledger) :
    ticket.position < terminalPosition outcome ∧ terminalPosition outcome < history.length :=
  (before ticket outcome terminal).order

end Leanux.Proofs.WG.AuthenticatedEffects.StagedProvenance
