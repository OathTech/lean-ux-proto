import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionIndexed
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationFirstTerminalSupport

/-! The native first-terminal cut moves one identified allocated ticket to
cleanup debt in the canonical ledger. Its evidence is supplied at that exact
history position; no arbitrary terminal label suffices for this transition. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open RetirementSecurity StagedProvenance

theorem entry_settle_allocated (before : StagedEntry.Inv history ledger debts locals w)
    (pending : (ticket,Status.pending (.allocated position ordinal)) ∈ ledger)
    (evidence : At history event ticket outcome) (quiet : birthPackets event = []) :
    StagedEntry.Inv (history ++ [event]) (settle [ticket] outcome ledger)
      (⟨ticket,position,ordinal,outcome⟩ :: debts) locals w := by
  have support : FirstTerminal.Support (births history) history ledger debts w :=
    ⟨before.core.physical,before.core.valid⟩
  obtain ⟨step,physical,_⟩ := support.settle pending outcome
  have chosen : ∀ t ∈ [ticket], t ∈ pendingAt (.allocated position ordinal) ledger := by
    intro t member
    have same := List.mem_singleton.mp member
    subst t
    exact mem_pendingAt.mpr pending
  have queues : QueueInv history (settle [ticket] outcome ledger) w := by
    intro generation pid stamp
    rw [settle_other_location (before.core.valid.1.symm ▸ before.core.valid.2) chosen (by simp)]
    exact before.core.queues generation pid stamp
  refine ⟨⟨?_,queues.append_history _,(before.core.selected.settled _ _).append _,
    physical.toPhysical.append _⟩,?_,(before.allocationLinks.settled _ _).append _,
    before.noSelected.settled _ _,before.packets,before.coverage,before.inventory⟩
  · rw [births_quiet history quiet]
    exact step.valid before.core.valid
  · exact (settle_at before.core.valid before.justified chosen
      (fun t member => List.mem_singleton.mp member ▸ evidence)).2

private theorem same_ticket {a b : Binding} (valid : Valid domain ledger)
    (left : a.pending ledger) (right : b.pending ledger)
    (recordedA : a.recorded history) (recordedB : b.recorded history)
    (same : a.ticket = b.ticket) : a.skb = b.skb := by
  unfold Binding.pending at left right
  have status := unique_status (valid.1.symm ▸ valid.2) (same ▸ left) right
  obtain ⟨position,ordinal⟩ := Pending.allocated.inj (Status.pending.inj status)
  have matched : Origin history b.position b.ordinal a.generation a.skb a.value := by
    simpa only [Binding.recorded,← position,← ordinal] using recordedA
  exact (matched.unique recordedB).2.1

private theorem same_cell {a b : Binding} (support : FirstTerminal.Support domain history ledger debts w)
    (left : a.pending ledger) (right : b.pending ledger)
    (recordedA : a.recorded history) (recordedB : b.recorded history)
    (same : a.skb = b.skb) :
    a.ticket = b.ticket ∧ a.position = b.position ∧ a.ordinal = b.ordinal := by
  unfold Binding.pending at left right
  have epochA := (support.resident _ _ _ left).at_origin recordedA
  have epochB := (support.resident _ _ _ right).at_origin recordedB
  have epoch : a.generation = b.generation := Option.some.inj (epochA.1.symm.trans epochB.1)
  have matched : Origin history a.position a.ordinal b.generation b.skb a.value := by
    simpa only [Binding.recorded,← epoch,← same] using recordedA
  have ticket := support.mixed _ _ _ (Or.inl left) _ _ _ (Or.inl right)
    _ _ _ _ matched recordedB
  have status := unique_status (support.valid.1.symm ▸ support.valid.2) (ticket ▸ left) right
  exact ⟨ticket,Pending.allocated.inj (Status.pending.inj status)⟩

theorem Cursor.settle_head (before : Cursor context (.sending (skb :: rest)) history ledger debts)
    (support : FirstTerminal.Support domain history ledger debts w)
    (unique : context.items.Nodup) (chosen : Binding) (member : chosen ∈ context.bindings)
    (head : chosen.skb = skb) (outcome : Staged.Obligations.Terminal) :
    Cursor context (.sending rest) history (settle [chosen.ticket] outcome ledger)
      (⟨chosen.ticket,chosen.position,chosen.ordinal,outcome⟩ :: debts) := by
  have pending := (before.assigned chosen member).1 (by simp [head])
  obtain ⟨step,_,terminal⟩ := support.settle pending outcome
  obtain ⟨left,split⟩ := before.remaining
  have tailUnique : (skb :: rest).Nodup := by
    rw [← split] at unique
    exact (List.nodup_append.mp unique).2.1
  refine ⟨before.step.trans step,before.recorded,?_,?_⟩
  · exact ⟨left ++ [skb],by simpa only [Phase.remaining,List.append_assoc,List.singleton_append] using split⟩
  · intro b inside
    constructor
    · intro still
      have old := (before.assigned b inside).1 (List.mem_cons_of_mem skb still)
      have different : b.ticket ≠ chosen.ticket := by
        intro same
        have cell := same_ticket support.valid old pending (before.recorded b inside)
          (before.recorded chosen member) same
        exact (List.nodup_cons.mp tailUnique).1 ((cell.trans head) ▸ still)
      exact List.mem_map.mpr ⟨(b.ticket,Status.pending (.allocated b.position b.ordinal)),old,
        by simp [different]⟩
    · intro done
      by_cases isHead : b.skb = skb
      · have old := (before.assigned b inside).1 (by simp [isHead])
        obtain ⟨ticket,position,ordinal⟩ := same_cell support old pending
          (before.recorded b inside) (before.recorded chosen member) (isHead.trans head.symm)
        exact ⟨outcome,by simp [ticket,position,ordinal],by simpa only [ticket] using terminal⟩
      · have oldDone : b.skb ∉ skb :: rest := by simp [isHead,done]
        obtain ⟨oldOutcome,debt,settled⟩ := (before.assigned b inside).2 oldDone
        exact ⟨oldOutcome,List.mem_cons_of_mem _ debt,step.terminal settled⟩

/-- Settlement changes the canonical entry and selected cursor together at
one source event. The chosen ticket is explicit for later source attribution. -/
theorem Owned.settle_head (before : Owned context (.sending (skb :: rest)) history ledger debts w)
    (chosen : Binding) (member : chosen ∈ context.bindings) (head : chosen.skb = skb)
    (evidence : At history event chosen.ticket outcome) (quiet : birthPackets event = []) :
    Owned context (.sending rest) (history ++ [event]) (settle [chosen.ticket] outcome ledger)
      (⟨chosen.ticket,chosen.position,chosen.ordinal,outcome⟩ :: debts) w := by
  have pending := (before.cursor.assigned chosen member).1 (by simp [head])
  have support : FirstTerminal.Support (births history) history ledger debts w.wg :=
    ⟨before.entry.core.physical,before.entry.core.valid⟩
  have unique : context.items.Nodup := (List.nodup_append.mp before.entry.inventory.localUnique).1
  exact ⟨(before.cursor.settle_head support unique chosen member head outcome).append _,
    entry_settle_allocated before.entry pending evidence quiet,
    (births_quiet history quiet).trans before.domain⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
