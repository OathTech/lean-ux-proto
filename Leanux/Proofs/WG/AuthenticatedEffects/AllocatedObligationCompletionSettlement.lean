import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionTimers

/-! Advancing one completion cursor settles the fixed ticket backed by its
actual selected cell. Other pending cells and already terminal cleanup debts
keep their identities. This algebra is used only after a native terminal cut. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity

private theorem same_pending_ticket {a b : Binding} (valid : Valid births ledger)
    (left : a.pending ledger) (right : b.pending ledger)
    (recordedA : a.recorded history) (recordedB : b.recorded history)
    (same : a.ticket = b.ticket) : a.skb = b.skb := by
  unfold Binding.pending at left right
  have status := unique_status (valid.1.symm ▸ valid.2) (same ▸ left) right
  obtain ⟨position,ordinal⟩ := Pending.allocated.inj (Status.pending.inj status)
  have matched : Origin history b.position b.ordinal a.generation a.skb a.value := by
    simpa only [Binding.recorded,← position,← ordinal] using recordedA
  exact (matched.unique recordedB).2.1

private theorem same_pending_cell {a b : Binding} (support : FirstTerminal.Support births history ledger debts w)
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

/-- The next native first-terminal result consumes exactly the head's fixed
ticket. The result remains cleanup debt in the same resident selected batch;
the caller still has to supply the actual terminal receipt. -/
theorem State.settle_head (before : State context (.sending (skb :: rest)) history w)
    (outcome : Staged.Obligations.Terminal) : State context (.sending rest) history w := by
  obtain ⟨ledger,debts,prior,support,recorded,suffix,assigned,coverage,inventory⟩ := before
  obtain ⟨left,split⟩ := suffix
  have member : skb ∈ context.items := by rw [← split]; simp [Phase.remaining]
  obtain ⟨chosen,chosenMember,chosenSkb⟩ := List.mem_map.mp member
  have pending := (assigned chosen chosenMember).1 (by simp [chosenSkb])
  obtain ⟨step,after,terminal⟩ := support.settle pending outcome
  have unique : context.items.Nodup := (List.nodup_append.mp inventory.localUnique).1
  have tailUnique : (skb :: rest).Nodup := by
    rw [← split] at unique
    exact (List.nodup_append.mp unique).2.1
  refine ⟨settle [chosen.ticket] outcome ledger,
    ⟨chosen.ticket,chosen.position,chosen.ordinal,outcome⟩ :: debts,
    prior.trans step,after,recorded,?_,?_,coverage,inventory⟩
  · exact ⟨left ++ [skb],by simpa only [Phase.remaining,List.append_assoc,List.singleton_append] using split⟩
  · intro b inside
    constructor
    · intro still
      have old := (assigned b inside).1 (List.mem_cons_of_mem skb still)
      have different : b.ticket ≠ chosen.ticket := by
        intro same
        have cell := same_pending_ticket support.valid old pending (recorded b inside)
          (recorded chosen chosenMember) same
        exact (List.nodup_cons.mp tailUnique).1 ((cell.trans chosenSkb) ▸ still)
      exact List.mem_map.mpr ⟨(b.ticket,Status.pending (.allocated b.position b.ordinal)),old,
        by simp [different]⟩
    · intro done
      by_cases isHead : b.skb = skb
      · have old := (assigned b inside).1 (by simp [isHead])
        obtain ⟨ticket,position,ordinal⟩ := same_pending_cell support old pending
          (recorded b inside) (recorded chosen chosenMember) (isHead.trans chosenSkb.symm)
        exact ⟨outcome,by simp [ticket,position,ordinal],by simpa only [ticket] using terminal⟩
      · have oldDone : b.skb ∉ skb :: rest := by simp [isHead,done]
        obtain ⟨oldOutcome,debt,settled⟩ := (assigned b inside).2 oldDone
        exact ⟨oldOutcome,List.mem_cons_of_mem _ debt,step.terminal settled⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
