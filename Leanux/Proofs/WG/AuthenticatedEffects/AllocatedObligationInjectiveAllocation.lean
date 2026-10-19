import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationInjectiveAssignment

/-! Actual native allocation preserves old pending cells and assigns each
selected ticket its own fresh batch ordinal. The native allocator's consecutive
ID result supplies both old/new separation and within-batch nonaliasing. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
variable {id : Nat}

theorem Origin.new_cell
    (origin : Origin (history ++ [.old (.allocated packets run)]) history.length ordinal generation id value) :
    run.value[ordinal]? = some id := by
  obtain ⟨otherPackets,otherRun,packet,atPosition,_,_,_,cell,_⟩ := origin
  have actual : (history ++ [CausalJournal.Event.old (.allocated packets run)])[history.length]? =
      some (.old (.allocated packets run)) := by simp
  have same := Option.some.inj (actual.symm.trans atPosition)
  cases same
  exact cell

theorem old_new_disjoint (backed : Backed history position ordinal run.before)
    (bounded : Packets.Inv run.before) (packets : List DataPacket)
    (valid : (run : WGRunWitness (List SkbId)).Valid (packets.mapM newTxSkb))
    (old : Origin history position ordinal generation id value)
    (fresh : Origin (history ++ [.old (.allocated packets run)]) history.length newOrdinal generation id newValue) :
    False := by
  obtain ⟨_,_,_,prior,_,_,outside,_⟩ := allocated_fresh_of_backed backed bounded packets valid
  obtain ⟨rfl,rfl,rfl⟩ := old.unique prior
  exact outside (List.mem_of_getElem? fresh.new_cell)

theorem Resident.assign_allocate (resident : Resident history ledger run.before)
    (bounded : Packets.Inv run.before) (packets : List DataPacket)
    (valid : (run : WGRunWitness (List SkbId)).Valid (packets.mapM newTxSkb))
    (device : run.before.dev = some d)
    (aligned : Aligned related (pendingAt (.selected takePosition) ledger) packets) :
    Resident (history ++ [.old (.allocated packets run)])
      (assignBatch takePosition history.length ledger) run.after := by
  intro ticket position ordinal member
  rcases assignBatch_cases member with old | fresh
  · exact ((resident ticket position ordinal old).allocate bounded packets valid).append _
  · obtain ⟨pending,rfl,rfl⟩ := fresh
    obtain ⟨packet,payload,_⟩ := aligned_at aligned (ticketOrdinal_get (mem_pendingAt.mpr pending))
    exact allocated history packets run valid device payload

theorem Injective.assign_allocate (injective : Injective history ledger)
    (resident : Resident history ledger run.before) (bounded : Packets.Inv run.before)
    (packets : List DataPacket) (valid : (run : WGRunWitness (List SkbId)).Valid (packets.mapM newTxSkb))
    (device : run.before.dev = some d) :
    Injective (history ++ [.old (.allocated packets run)]) (assignBatch takePosition history.length ledger) := by
  intro first firstPosition firstOrdinal firstMember second secondPosition secondOrdinal secondMember
    generation id firstValue secondValue firstOrigin secondOrigin
  rcases assignBatch_cases firstMember with firstOld | firstNew
  · have oldFirst := firstOrigin.prefix (resident.position_lt firstOld)
    rcases assignBatch_cases secondMember with secondOld | secondNew
    · exact injective first firstPosition firstOrdinal firstOld second secondPosition secondOrdinal secondOld
        generation id firstValue secondValue oldFirst
        (secondOrigin.prefix (resident.position_lt secondOld))
    · obtain ⟨_,rfl,_⟩ := secondNew
      exact False.elim (old_new_disjoint (resident first firstPosition firstOrdinal firstOld)
        bounded packets valid oldFirst secondOrigin)
  · obtain ⟨firstPending,rfl,firstIndex⟩ := firstNew
    rcases assignBatch_cases secondMember with secondOld | secondNew
    · exact False.elim (old_new_disjoint (resident second secondPosition secondOrdinal secondOld)
        bounded packets valid (secondOrigin.prefix (resident.position_lt secondOld)) firstOrigin)
    · obtain ⟨secondPending,rfl,secondIndex⟩ := secondNew
      have sameOrdinal := nodup_ordinal (TxDisposition.ItemSeparation.allocate_nodup device valid)
        firstOrigin.new_cell secondOrigin.new_cell
      have firstAt := ticketOrdinal_get (mem_pendingAt.mpr firstPending)
      have secondAt := ticketOrdinal_get (mem_pendingAt.mpr secondPending)
      rw [←firstIndex] at firstAt
      rw [←secondIndex,←sameOrdinal] at secondAt
      exact Option.some.inj (firstAt.symm.trans secondAt)

/-- A completed actual allocation extends the fixed ledger with no new tickets:
the exact selected list moves to its native batch ordinals, old pending cells
remain resident, and per-cell injectivity is retained. Initialization, the
source's selected/queue frontier, and stopped allocation prefixes remain outside
this local native-call contract. -/
theorem allocate_assigned (validLedger : Valid births ledger)
    (resident : Resident history ledger run.before) (injective : Injective history ledger)
    (bounded : Packets.Inv run.before) (packets : List DataPacket)
    (valid : (run : WGRunWitness (List SkbId)).Valid (packets.mapM newTxSkb))
    (device : run.before.dev = some d)
    (aligned : Aligned related (pendingAt (.selected takePosition) ledger) packets) :
    let after := assignBatch takePosition history.length ledger
    TransmitSecurity.Staged.Obligations.Step ledger after ∧ Valid births after ∧
      (pendingAt (.selected takePosition) ledger).Nodup ∧
      Resident (history ++ [.old (.allocated packets run)]) after run.after ∧
      Injective (history ++ [.old (.allocated packets run)]) after ∧
      (∀ ordinal ticket, (pendingAt (.selected takePosition) ledger)[ordinal]? = some ticket →
        (ticket,Status.pending (.allocated history.length ordinal)) ∈ after) := by
  have step := assignBatch_step takePosition history.length ledger
  have unique : (keys ledger).Nodup := validLedger.1.symm ▸ validLedger.2
  exact ⟨step,step.valid validLedger,pendingAt_unique unique _,
    resident.assign_allocate bounded packets valid device aligned,
    injective.assign_allocate resident bounded packets valid device,
    fun _ _ atTicket => assignBatch_at validLedger atTicket⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
