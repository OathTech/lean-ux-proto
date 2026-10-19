import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCleanupPrimitiveRuns
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCleanupCuts

/-! Ordinary completion has already assigned each packet's first terminal
outcome. The native erase consumes its physical debt on the unchanged ledger,
before the lifetime release event; no new disposal receipt is needed. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.OrdinaryCleanup
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations AllocatedObligation CompletionBatch CompleteCarrier

theorem head_debt
    (before : Owned context (.freeing (skb :: rest)) history ledger debts w)
    (epoch : Packets.epoch w.wg=some generation) :
    ∃ debt ∈ debts, ∃ value,
      Origin history debt.position debt.ordinal generation skb value ∧
      (debt.ticket,Status.terminal debt.outcome)∈ledger := by
  have inItems : skb∈context.items := by
    obtain ⟨left,equal⟩ := before.cursor.remaining
    rw [←equal]
    simp [Phase.remaining]
  obtain ⟨binding,member,same⟩ := List.mem_map.mp inItems
  obtain ⟨outcome,debt,terminal⟩ := (before.cursor.assigned binding member).2 (by simp [same])
  let chosen : CleanupDebt := ⟨binding.ticket,binding.position,binding.ordinal,outcome⟩
  have origin : Origin history chosen.position chosen.ordinal binding.generation skb binding.value := by
    simpa only [Binding.recorded,chosen,same] using before.cursor.recorded binding member
  have actual := ((before.entry.core.physical.cleanup chosen debt).2.at_origin origin).1
  have sameEpoch := Option.some.inj (actual.symm.trans epoch)
  exact ⟨chosen,debt,binding.value,sameEpoch ▸ origin,terminal⟩

/-- The account holds on the actual post-erase world and the earlier history.
Only the exact freed cell's debts and selected local are removed. -/
theorem native_accounted
    (before : Owned context (.freeing (skb :: rest)) history ledger debts w)
    (complete : StagedTerminalComplete.Complete history ledger)
    (epoch : Packets.epoch w.wg=some generation)
    (native : (liftWG (freeTxSkb skb)).run w=.ok ((),v)) :
    Accounted history ledger (forgetFreedCell history generation skb debts)
      (⟨.selected,context.pid,rest⟩ :: context.locals) v.wg := by
  obtain ⟨debt,member,value,origin,_⟩ := head_debt before epoch
  obtain ⟨resident,mixed,covered,cleanup,_,_⟩ := cleanup_native_mixed native
    before.entry.core.valid before.entry.core.physical.mixed before.entry.core.physical.resident
    before.entry.core.physical.covered before.entry.core.physical.cleanup debt member origin epoch
  obtain ⟨coverage,inventory⟩ := free_ownership before.entry.coverage before.entry.inventory native
  obtain ⟨bounded,queues⟩ := free_entry_facts before.entry.packets native
  have keptEpoch := (FirstTerminal.cleanup_views skb w v native).1
  refine ⟨⟨⟨before.entry.core.valid,?_,before.entry.core.selected,⟨resident,covered,cleanup,mixed⟩⟩,
    before.entry.justified,before.entry.allocationLinks,before.entry.noSelected,bounded,coverage,inventory⟩,complete⟩
  simpa only [List.append_nil] using before.entry.core.queues.views_append [] keptEpoch queues

/-- At each fixed erase/release phase the same first-terminal ledger has a
complete native account with the consumed cleanup debt. The access markers
do not settle the packet a second time. -/
theorem phase_accounted (phase : CleanupPrimitive.Phase)
    (before : Owned context (.freeing (skb :: rest)) history ledger debts w)
    (complete : StagedTerminalComplete.Complete history ledger)
    (epoch : Packets.epoch w.wg=some generation)
    (native : (liftWG (freeTxSkb skb)).run w=.ok ((),v)) :
    Accounted (CleanupPrimitive.current phase w skb history) ledger
      (forgetFreedCell history generation skb debts)
      (⟨.selected,context.pid,rest⟩ :: context.locals) v.wg := by
  have after := native_accounted before complete epoch native
  cases phase with
  | mutated =>
      exact after.append_quiet [CleanupPrimitive.readEvent w.wg skb]
        (by intro event member; cases List.mem_singleton.mp member; rfl)
        (by intro event member; cases List.mem_singleton.mp member; intro position; rfl)
  | released =>
      apply after.append_quiet [CleanupPrimitive.readEvent w.wg skb,CleanupPrimitive.releaseEvent w.wg skb]
      · intro event member
        rcases List.mem_cons.mp member with rfl | tail
        · rfl
        · cases List.mem_singleton.mp tail; rfl
      · intro event member position
        rcases List.mem_cons.mp member with rfl | tail
        · rfl
        · cases List.mem_singleton.mp tail; rfl

/-- The native erase discharges a debt for this exact allocation and keeps
its original terminal outcome. Retaining that old debt as resident is false. -/
theorem native_consumes
    (before : Owned context (.freeing (skb :: rest)) history ledger debts w)
    (epoch : Packets.epoch w.wg=some generation)
    (native : (liftWG (freeTxSkb skb)).run w=.ok ((),v)) :
    ∃ debt ∈ debts,
      (debt.ticket,Status.terminal debt.outcome)∈ledger ∧
      debt∉forgetFreedCell history generation skb debts ∧
      PacketMaterial.view v.wg skb=none := by
  obtain ⟨debt,member,value,origin,terminal⟩ := head_debt before epoch
  refine ⟨debt,member,terminal,?_,(FirstTerminal.cleanup_views skb w v native).2.1⟩
  intro retained
  exact (mem_forgetFreedCell.mp retained).2 ⟨value,origin⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.OrdinaryCleanup
