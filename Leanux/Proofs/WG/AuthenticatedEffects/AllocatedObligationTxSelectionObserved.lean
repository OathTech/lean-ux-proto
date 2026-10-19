import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationTxSelectionHistoryFrames

/-! Full entry transport at the actual final journal's queue peek and remove
cuts. Source history and native ownership are established separately and then
joined at the same run, with no event chronology inferred from erasure. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.TxSelection
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations CreateDisposal
set_option pp.structureInstances false

theorem peek_entry (pid : PeerId) (before : StagedEntry.Inv history ledger [] locals w.wg)
    (performed : runPrefix (peek pid) w history = (.ok (first,v),last)) :
    StagedEntry.Inv last ledger [] locals v.wg ∧
    (∀ p, peerAt v.wg pid = some p → p.txQueue.peeked = first) ∧
    (∀ items, first = some items → PendingBatch last ledger items) := by
  have full := (peek_erases pid w history).symm.trans (congrArg Prod.fst performed)
  obtain ⟨suffix,extended,quiet⟩ := peek_birth_quiet pid w history
  rw [performed] at extended
  change last = history ++ suffix at extended
  rw [liftWG_run] at full
  cases native : ((txPeekSource pid).run w.wg).run w.ambient with
  | error stop => simp [native,Except.map] at full
  | ok out =>
    obtain ⟨⟨result,g⟩,ambient⟩ := out
    simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at full
    obtain ⟨rfl,rfl⟩ := full
    obtain ⟨entry,cached,pending⟩ := peek_native pid w.ambient ambient before native
    rw [extended]
    exact ⟨entry.views suffix quiet rfl rfl rfl rfl rfl rfl,cached,
      fun items selected => (pending items selected).append suffix⟩

/-- Removing the actual cached queue entry transfers ownership to the
selected local. At the debt-free worker boundary every selected cell is
assigned to a pending ticket of its exact allocation occurrence. -/
theorem drop_entry (pid : PeerId) (items : List SkbId)
    (before : StagedEntry.Inv history ledger [] locals w.wg)
    (cached : ∀ p, peerAt w.wg pid = some p → p.txQueue.peeked = some items)
    (performed : runPrefix (CausalJournal.completionOps.drop pid items) w history = (.ok ((),v),last)) :
    StagedEntry.Inv last ledger [] (⟨.selected,pid,items⟩ :: locals) v.wg ∧ PendingBatch last ledger items := by
  have full := (drop_erases pid items w history).symm.trans (congrArg Prod.fst performed)
  obtain ⟨suffix,extended,quiet⟩ := drop_birth_quiet pid items w history
  rw [performed] at extended
  change last = history ++ suffix at extended
  rw [liftWG_run] at full
  cases native : ((txDropSource pid).run w.wg).run w.ambient with
  | error stop => simp [native,Except.map] at full
  | ok out =>
    obtain ⟨⟨ignored,g⟩,ambient⟩ := out
    cases ignored
    simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at full
    obtain ⟨_,rfl⟩ := full
    have entry := drop_native pid w.ambient ambient before cached native
    have final := entry.views suffix quiet rfl rfl rfl rfl rfl rfl
    rw [extended]
    exact ⟨final,DeadEntry.selected_pending final⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.TxSelection
