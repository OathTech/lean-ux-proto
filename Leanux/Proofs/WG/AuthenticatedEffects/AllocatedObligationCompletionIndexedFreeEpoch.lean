import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionIndexedFree

/-! Refine the existing total native free with its actual device epoch.
The refinement is derived from backing before and after that same free;
the original theorem is unchanged. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open TransmitSecurity.Staged.Obligations

/-- The cleanup filter names the actual entry epoch. A wrong epoch would
retain the freed cell's debt, contradicting its native post-free backing. -/
theorem indexed_free_total_epoch
    (before : Owned context (.freeing (skb :: rest)) history ledger debts w) :
    ∃ v suffix generation, Packets.epoch w.wg = some generation ∧
      runPrefix (FirstTerminal.cleanupFree skb) w history = (.ok ((),v),history ++ suffix) ∧
      Owned context (.freeing rest) (history ++ suffix) ledger
        (forgetFreedCell history generation skb debts) v := by
  obtain ⟨v,suffix,generation,run,after⟩ := indexed_free_total before
  refine ⟨v,suffix,generation,?_,run,after⟩
  have inItems : skb ∈ context.items := by
    obtain ⟨left,equal⟩ := before.cursor.remaining
    rw [← equal]
    simp [Phase.remaining]
  obtain ⟨binding,member,head⟩ := List.mem_map.mp inItems
  obtain ⟨outcome,debt,_⟩ := (before.cursor.assigned binding member).2 (by simp [head])
  let chosen : CleanupDebt := ⟨binding.ticket,binding.position,binding.ordinal,outcome⟩
  have origin : Origin history chosen.position chosen.ordinal binding.generation skb binding.value := by
    simpa only [chosen,Binding.recorded,head] using before.cursor.recorded binding member
  have oldEpoch := ((before.entry.core.physical.cleanup chosen debt).2.at_origin origin).1
  apply Classical.byContradiction
  intro different
  have retained : chosen ∈ forgetFreedCell history generation skb debts := by
    apply mem_forgetFreedCell.mpr
    refine ⟨debt,?_⟩
    rintro ⟨value,other⟩
    exact different (oldEpoch.trans (congrArg some (origin.unique other).1))
  have cell := ((after.entry.core.physical.cleanup chosen retained).2.at_origin (origin.append suffix)).2
  have native := (FirstTerminal.cleanupFree_erases skb w history).symm.trans (congrArg Prod.fst run)
  have erased := (native_free_views skb w v native).2.1
  rw [erased] at cell
  cases cell

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
