import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCoverageFrames

/-! Every new native TX cell receives the corresponding incoming selected
fixed ticket at its actual ordinal. Old pending cells and terminal cleanup
cells retain their allocation identities. No initialized frontier is assumed. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
variable {id : Nat}

private theorem aligned_length {α β : Type} {related : α → β → Prop}
    {left : List α} {right : List β} (aligned : Aligned related left right) :
    left.length = right.length := by
  induction aligned with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons,ih]

theorem Tracked.assign (tracked : Tracked ledger debts ticket position ordinal) :
    Tracked (assignBatch takePosition batchPosition ledger) debts ticket position ordinal := by
  rcases tracked with pending | ⟨outcome,debt,terminal⟩
  · exact Or.inl (List.mem_map.mpr ⟨_,pending,rfl⟩)
  · exact Or.inr ⟨outcome,debt,(assignBatch_step _ _ _).terminal terminal⟩

/-- Converse coverage uses exact native allocation output, not just an
absence-of-alias premise or a fresh existential ticket for each cell. -/
theorem Covered.assign_allocate (covered : Covered history ledger debts run.before)
    (validLedger : Valid births ledger) (packets : List DataPacket)
    (valid : (run : WGRunWitness (List SkbId)).Valid (packets.mapM newTxSkb))
    (device : run.before.dev = some d)
    (aligned : Aligned related (pendingAt (.selected takePosition) ledger) packets) :
    Covered (history ++ [.old (.allocated packets run)])
      (assignBatch takePosition history.length ledger) debts run.after := by
  obtain ⟨itemEq,_,after,afterDevice,_,sameEpoch,_⟩ :=
    TxDisposition.ItemSeparation.allocate_result packets device valid
  have epoch : Packets.epoch run.after = Packets.epoch run.before := by
    simp only [Packets.epoch,device,afterDevice,Option.map_some,sameEpoch]
  intro id value cell
  obtain ⟨packet,resident,material⟩ := Option.map_eq_some_iff.mp cell
  rcases RetirementSecurity.allocate_survivor packets run.ambientBefore run.ambientAfter valid resident with fresh | old
  · obtain ⟨ordinal,atId⟩ := List.mem_iff_getElem?.mp fresh
    have bound : ordinal < (pendingAt (.selected takePosition) ledger).length := by
      have below := (List.getElem?_eq_some_iff.mp atId).1
      rw [itemEq,List.length_range'] at below
      rw [aligned_length aligned]
      exact below
    let ticket := (pendingAt (.selected takePosition) ledger)[ordinal]
    have atTicket : (pendingAt (.selected takePosition) ledger)[ordinal]? = some ticket :=
      List.getElem?_eq_getElem bound
    obtain ⟨original,newId,_,_,sameId,origin,stored,_⟩ :=
      allocated_ticket history packets run valid device aligned atTicket
    have same : newId = id := Option.some.inj (sameId.symm.trans atId)
    subst newId
    have valueSame : PacketMaterial.material original = value := Option.some.inj (stored.symm.trans cell)
    refine ⟨d.ifindex,ticket,history.length,ordinal,?_,?_,Or.inl (assignBatch_at validLedger atTicket)⟩
    · simp only [Packets.epoch,afterDevice,Option.map_some,sameEpoch]
    · exact valueSame ▸ origin
  · have oldCell : PacketMaterial.view run.before id = some value := by
      simp only [PacketMaterial.view,old,Option.map_some,material]
    obtain ⟨generation,ticket,position,ordinal,time,origin,tracked⟩ := covered id value oldCell
    exact ⟨generation,ticket,position,ordinal,epoch.trans time,origin.append _,tracked.assign⟩

theorem DebtsResident.assign_allocate (resident : DebtsResident history ledger debts run.before)
    (bounded : Packets.Inv run.before) (packets : List DataPacket)
    (valid : (run : WGRunWitness (List SkbId)).Valid (packets.mapM newTxSkb)) :
    DebtsResident (history ++ [.old (.allocated packets run)])
      (assignBatch takePosition history.length ledger) debts run.after := by
  intro debt member
  obtain ⟨terminal,backed⟩ := resident debt member
  exact ⟨(assignBatch_step _ _ _).terminal terminal,(backed.allocate bounded packets valid).append _⟩

/-- The same local allocation preserves both directions of ticket/cell backing
and the native queue-or-held ownership inventory. The new batch is explicitly
held unpublished; a later publication/disposal must transfer that owner. -/
theorem allocate_covered
    (validLedger : Valid births ledger) (resident : Resident history ledger run.before)
    (injective : Injective history ledger) (covered : Covered history ledger debts run.before)
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
      Resident events after run.after ∧ Injective events after ∧ Covered events after debts run.after ∧
      DebtsResident events after debts run.after ∧ RetirementSecurity.TxCoverage held run.after ∧
      RetirementSecurity.TxInventory held run.after := by
  have assigned := allocate_assigned validLedger resident injective bounded packets valid device aligned
  exact ⟨assigned.1,assigned.2.1,assigned.2.2.2.1,assigned.2.2.2.2.1,
    covered.assign_allocate validLedger packets valid device aligned,
    cleanup.assign_allocate bounded packets valid,
    ownership.allocate pid packets run.ambientBefore run.ambientAfter valid,
    inventory.allocate bounded device pid packets run.ambientBefore run.ambientAfter valid⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
