import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteConsequencesReceipts

/-! The admission domain counts packet positions at the successful routing
splice, plus the actual new keepalive. Early invocation errors are accounted
separately by the native txErrors theorem, not as per-segment admissions. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteConsequences
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open RetirementSecurity AllocatedObligation CausalJournal StagedProvenance StagedTerminalComplete

theorem fresh_member (present : packets[ordinal]? = some packet) :
    (⟨position,first+ordinal⟩ : Ticket) ∈ freshTickets position first packets := by
  induction packets generalizing first ordinal with
  | nil => simp at present
  | cons head tail ih =>
    cases ordinal with
    | zero => simp [freshTickets]
    | succ n =>
      have later := ih (first:=first+1) present
      apply List.mem_cons_of_mem
      simpa only [Nat.add_assoc,Nat.add_comm 1 n] using later

theorem birth_member (historyEq : history=pre++event::post)
    (present : (birthPackets event)[ordinal]? = some packet) :
    (⟨pre.length,ordinal⟩ : Ticket) ∈ births history := by
  rw [historyEq,births,birthsFrom_append]
  apply List.mem_append_right
  change (⟨pre.length,ordinal⟩ : Ticket) ∈
    freshTickets (0+pre.length) 0 (birthPackets event) ++ birthsFrom _ post
  apply List.mem_append_left
  simpa only [Nat.zero_add] using fresh_member (position:=pre.length) (first:=0) present

/-- Every successful routed packet position receives one status in the same
ledger, even when several admitted positions contain equal plaintext bytes. -/
theorem Cut.routed (cut : Cut history ledger debts locals w)
    (historyEq : history=pre++(.old (.routed family addr packets mtu run))::post)
    (accepted : run.value = .ok pid)
    (present : (packets.map (fun packet=>{packet with mtu}))[ordinal]? = some packet) :
    ∃ status, (⟨pre.length,ordinal⟩,status) ∈ ledger ∧
      StatusEvidence history ledger locals w ⟨pre.length,ordinal⟩ status ∧
      ∀ other, (⟨pre.length,ordinal⟩,other) ∈ ledger → other=status := by
  apply cut.partition
  apply birth_member historyEq
  simpa only [birthPackets,accepted] using present

/-- A true keepalive callback creates a ticket only when it entered with an
empty staged queue; merely revisiting an existing queue creates none. -/
theorem Cut.keepalive (cut : Cut history ledger debts locals w)
    (historyEq : history=pre++(.keepalivePrepared pid run)::post)
    (accepted : run.value = true) (empty : Staged.stagedAt run.before pid = some (stamp,[])) :
    ∃ status, (⟨pre.length,0⟩,status) ∈ ledger ∧
      StatusEvidence history ledger locals w ⟨pre.length,0⟩ status ∧
      ∀ other, (⟨pre.length,0⟩,other) ∈ ledger → other=status := by
  apply cut.partition
  apply birth_member historyEq (packet:={})
  simp only [birthPackets,accepted,empty,↓reduceIte,List.getElem?_cons_zero]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteConsequences
