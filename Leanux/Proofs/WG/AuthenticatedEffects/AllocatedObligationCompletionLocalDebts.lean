import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionIndexedFreeEpoch
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionIndexedSend

/-! At the idle worker boundary there are no old cleanup debts. New completion
debts belong to this concrete selected batch, then to its remaining free loop.
Consequently finishing all native frees restores the empty incoming debt list. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open TransmitSecurity.Staged.Obligations

def LocalDebts (context : Context) (remaining : List SkbId) (debts : List CleanupDebt) : Prop :=
  ∀ debt ∈ debts, ∃ binding : Binding, binding ∈ context.bindings ∧
    debt.position = binding.position ∧ debt.ordinal = binding.ordinal ∧ binding.skb ∈ remaining

theorem LocalDebts.empty (context : Context) (remaining : List SkbId) : LocalDebts context remaining [] := by
  intro debt member
  cases member

theorem LocalDebts.settle (before : LocalDebts context context.items debts)
    (member : binding ∈ context.bindings) (outcome : Staged.Obligations.Terminal) :
    LocalDebts context context.items (⟨binding.ticket,binding.position,binding.ordinal,outcome⟩ :: debts) := by
  intro debt inside
  rcases List.mem_cons.mp inside with rfl | old
  · exact ⟨binding,member,rfl,rfl,List.mem_map.mpr ⟨binding,member,rfl⟩⟩
  · exact before debt old

theorem LocalDebts.finished (before : LocalDebts context [] debts) : debts = [] := by
  cases debts with
  | nil => rfl
  | cons debt tail =>
    obtain ⟨binding,_,_,_,impossible⟩ := before debt (by simp)
    cases impossible

/-- Exact cleanup removes every debt referring to the freed native cell and
retains only debts belonging to the actual remaining selected local. -/
theorem LocalDebts.free
    (before : Owned context (.freeing (skb :: rest)) history ledger debts w)
    (localDebts : LocalDebts context (skb :: rest) debts)
    (epoch : Packets.epoch w.wg = some generation) :
    LocalDebts context rest (forgetFreedCell history generation skb debts) := by
  intro debt member
  obtain ⟨old,notRefers⟩ := mem_forgetFreedCell.mp member
  obtain ⟨binding,inside,position,ordinal,inRest⟩ := localDebts debt old
  refine ⟨binding,inside,position,ordinal,?_⟩
  rcases List.mem_cons.mp inRest with same | kept
  · have origin : Origin history debt.position debt.ordinal binding.generation skb binding.value := by
      rw [position,ordinal,← same]
      exact before.cursor.recorded binding inside
    have actualEpoch := ((before.entry.core.physical.cleanup debt old).2.at_origin origin).1
    have equal := Option.some.inj (actualEpoch.symm.trans epoch)
    exact False.elim (notRefers ⟨binding.value,equal ▸ origin⟩)
  · exact kept

/-- The actual native free is total and keeps both the indexed semantic
entry and its local cleanup-debt invariant on the exact successor list. -/
theorem indexed_free_local
    (before : Owned context (.freeing (skb :: rest)) history ledger debts w)
    (localDebts : LocalDebts context (skb :: rest) debts) :
    ∃ v suffix generation,
      runPrefix (FirstTerminal.cleanupFree skb) w history = (.ok ((),v),history ++ suffix) ∧
      Owned context (.freeing rest) (history ++ suffix) ledger
        (forgetFreedCell history generation skb debts) v ∧
      LocalDebts context rest (forgetFreedCell history generation skb debts) := by
  obtain ⟨v,suffix,generation,epoch,run,after⟩ := indexed_free_total_epoch before
  exact ⟨v,suffix,generation,run,after,localDebts.free before epoch⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
