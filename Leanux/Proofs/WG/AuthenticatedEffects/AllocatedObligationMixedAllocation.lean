import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationMixedFrames

/-! Native allocation is fresh against both pending cells and terminal cells
awaiting cleanup. The selected fixed tickets keep the native batch ordinals;
no numeric-slot or final conservation assumption supplies separation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations

theorem Tracked.assign_cases (cleanup : DebtsResident history ledger debts w)
    (tracked : Tracked (assignBatch takePosition batchPosition ledger) debts ticket position ordinal) :
    Tracked ledger debts ticket position ordinal ∨
      ((ticket,Status.pending (.selected takePosition)) ∈ ledger ∧ position = batchPosition ∧
        ordinal = ticketOrdinal ticket (pendingAt (.selected takePosition) ledger)) := by
  rcases tracked with pending | ⟨outcome,debt,_⟩
  · rcases assignBatch_cases pending with old | fresh
    · exact Or.inl (Or.inl old)
    · exact Or.inr fresh
  · exact Or.inl (Or.inr ⟨outcome,debt,(cleanup _ debt).1⟩)

/-- Every old tracked allocation is physically resident, including debts;
therefore the native nextSkb frontier excludes all old/new cell collisions. -/
theorem MixedInjective.assign_allocate (mixed : MixedInjective history ledger debts)
    (resident : Resident history ledger run.before) (cleanup : DebtsResident history ledger debts run.before)
    (bounded : Packets.Inv run.before) (packets : List DataPacket)
    (valid : (run : WGRunWitness (List SkbId)).Valid (packets.mapM newTxSkb))
    (device : run.before.dev = some d) :
    MixedInjective (history ++ [.old (.allocated packets run)])
      (assignBatch takePosition history.length ledger) debts := by
  intro first firstPosition firstOrdinal firstTracked second secondPosition secondOrdinal secondTracked
    generation id firstValue secondValue firstOrigin secondOrigin
  rcases firstTracked.assign_cases cleanup with firstOld | firstNew
  · have oldFirst := firstOrigin.prefix (firstOld.position_lt resident cleanup)
    rcases secondTracked.assign_cases cleanup with secondOld | secondNew
    · exact mixed first firstPosition firstOrdinal firstOld second secondPosition secondOrdinal secondOld
        generation id firstValue secondValue oldFirst
        (secondOrigin.prefix (secondOld.position_lt resident cleanup))
    · obtain ⟨_,rfl,_⟩ := secondNew
      exact False.elim (old_new_disjoint (firstOld.backed resident cleanup)
        bounded packets valid oldFirst secondOrigin)
  · obtain ⟨firstPending,rfl,firstIndex⟩ := firstNew
    rcases secondTracked.assign_cases cleanup with secondOld | secondNew
    · exact False.elim (old_new_disjoint (secondOld.backed resident cleanup)
        bounded packets valid (secondOrigin.prefix (secondOld.position_lt resident cleanup)) firstOrigin)
    · obtain ⟨secondPending,rfl,secondIndex⟩ := secondNew
      have sameOrdinal := nodup_ordinal (TxDisposition.ItemSeparation.allocate_nodup device valid)
        firstOrigin.new_cell secondOrigin.new_cell
      have firstAt := ticketOrdinal_get (mem_pendingAt.mpr firstPending)
      have secondAt := ticketOrdinal_get (mem_pendingAt.mpr secondPending)
      rw [←firstIndex] at firstAt
      rw [←secondIndex,←sameOrdinal] at secondAt
      exact Option.some.inj (firstAt.symm.trans secondAt)

/-- The actual completed allocator retains two-way coverage and mixed logical
uniqueness, with explicit unpublished ownership of the new native batch. -/
theorem allocate_mixed_covered
    (validLedger : Valid births ledger) (resident : Resident history ledger run.before)
    (mixed : MixedInjective history ledger debts) (covered : Covered history ledger debts run.before)
    (cleanup : DebtsResident history ledger debts run.before)
    (bounded : Packets.Inv run.before)
    (ownership : RetirementSecurity.TxCoverage locals run.before)
    (inventory : RetirementSecurity.TxInventory locals run.before)
    (pid : PeerId) (packets : List DataPacket)
    (valid : (run : WGRunWitness (List SkbId)).Valid (packets.mapM newTxSkb))
    (device : run.before.dev = some d)
    (aligned : Aligned related (pendingAt (.selected takePosition) ledger) packets) :
    let after := assignBatch takePosition history.length ledger
    let events := history ++ [.old (.allocated packets run)]
    let held := RetirementSecurity.TxLocalBatch.mk .unpublished pid run.value :: locals
    TransmitSecurity.Staged.Obligations.Step ledger after ∧ Valid births after ∧
      Resident events after run.after ∧ MixedInjective events after debts ∧
      Covered events after debts run.after ∧ DebtsResident events after debts run.after ∧
      RetirementSecurity.TxCoverage held run.after ∧ RetirementSecurity.TxInventory held run.after := by
  have transported := allocate_covered validLedger resident mixed.pending covered cleanup bounded
    ownership inventory pid packets valid device aligned
  exact ⟨transported.1,transported.2.1,transported.2.2.1,
    mixed.assign_allocate resident cleanup bounded packets valid device,
    transported.2.2.2.2⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
