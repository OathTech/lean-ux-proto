import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionIndexed
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationReleaseCarrier

/-! The release receipt settles the same indexed ledger as the completion
cursor. Native packet-store and physical-owner transport are explicit source
cut inputs here; this is not an initialized release theorem. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open RetirementSecurity Staged StagedProvenance HandshakeSecurity.StagedDisposal

theorem release_none_entry (peer : Option PeerId)
    (r : WGRunWitness (Option (PeerId × Peer))) (native : r.Valid (releaseCut peer))
    (value : r.value = none) (before : StagedEntry.Inv history ledger debts locals r.before)
    (packets : Packets.Inv r.after) (coverage : TxCoverage locals r.after)
    (inventory : TxInventory locals r.after) :
    StagedEntry.Inv (history ++ [.stagedDisposal (.release peer r)]) ledger debts locals r.after :=
  ⟨core_release_none peer r native value before.core,before.justified.append _,
    before.allocationLinks.append _,before.noSelected,packets,coverage,inventory⟩

/-- A final release disposes exactly the staged tickets charged at this
native receipt. Allocation bindings and earlier terminal outcomes survive in
the same successor ledger, with their provenance and cleanup debt intact. -/
theorem release_final_entry (peer : Option PeerId)
    (r : WGRunWitness (Option (PeerId × Peer))) (native : r.Valid (releaseCut peer))
    (value : r.value = some (pid,p)) (before : StagedEntry.Inv history ledger debts locals r.before)
    (packets : Packets.Inv r.after) (coverage : TxCoverage locals r.after)
    (inventory : TxInventory locals r.after) :
    ∃ generation, Packets.epoch r.before = some generation ∧
      let chosen := pendingAt (.staged generation pid p.internalId) ledger
      let after := settle chosen (.counted history.length .finalRelease) ledger
      Staged.Obligations.Step ledger after ∧ AllocatedFrame ledger after ∧
        StagedEntry.Inv (history ++ [.stagedDisposal (.release peer r)]) after debts locals r.after ∧
        (∀ ticket ∈ chosen, (ticket,Status.terminal (.counted history.length .finalRelease)) ∈ after) ∧
        (∃ count, dropped r.before = some count ∧ dropped r.after = some (count + chosen.length)) := by
  obtain ⟨generation,epoch,step,core,terminal,charged⟩ :=
    core_release_final peer r native value before.core
  have frame := settle_allocated_frame before.core.valid
    (fun ticket (member : ticket ∈ pendingAt (.staged generation pid p.internalId) ledger) => member)
    (by intro _ _; simp) (.counted history.length .finalRelease)
  have provenance := (StagedProvenance.released peer r native value epoch
    before.core.queues before.core.valid before.justified).2
  exact ⟨generation,epoch,step,frame,⟨core,provenance,
    (before.allocationLinks.frame frame).append _,before.noSelected.settled _ _,
    packets,coverage,inventory⟩,terminal,charged⟩

/-- The completion cursor crosses the counted native release with the same
ticket identities; no unrelated existential completion state is consulted. -/
theorem Owned.release_final (peer : Option PeerId)
    (r : WGRunWitness (Option (PeerId × Peer))) (native : r.Valid (releaseCut peer))
    (value : r.value = some (pid,p)) (sameBefore : w.wg = r.before) (sameAfter : v.wg = r.after)
    (before : Owned context phase history ledger debts w)
    (packets : Packets.Inv r.after)
    (coverage : TxCoverage (⟨.selected,context.pid,phase.active context⟩ :: context.locals) r.after)
    (inventory : TxInventory (⟨.selected,context.pid,phase.active context⟩ :: context.locals) r.after) :
    ∃ generation, Packets.epoch r.before = some generation ∧
      let chosen := pendingAt (.staged generation pid p.internalId) ledger
      let after := settle chosen (.counted history.length .finalRelease) ledger
      Owned context phase (history ++ [.stagedDisposal (.release peer r)]) after debts v ∧
        (∀ ticket ∈ chosen, (ticket,Status.terminal (.counted history.length .finalRelease)) ∈ after) ∧
        (∃ count, dropped r.before = some count ∧ dropped r.after = some (count + chosen.length)) := by
  obtain ⟨generation,epoch,step,frame,entry,terminal,charged⟩ :=
    release_final_entry peer r native value (sameBefore ▸ before.entry) packets coverage inventory
  refine ⟨generation,epoch,?_,terminal,charged⟩
  apply before.advance step frame _ (sameAfter.symm ▸ entry)
  exact births_quiet history rfl

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
