import Leanux.Proofs.WG.TransmitSecurity.StagedObligationAllocationFrames

/-! The completed native allocator transports the whole canonical ledger.
The caller supplies the selected batch relation and native allocation-frontier
invariant; the result keeps its actual unpublished batch and every old debt. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
open Leanux Leanux.WG Leanux.Proofs.Logged Staged.Origins Lifetimes
open AuthenticatedEffects CausalJournal AllocatedObligation

theorem core_allocate (before : Core history ledger debts run.before)
    (bounded : Packets.Inv run.before)
    (ownership : RetirementSecurity.TxCoverage locals run.before)
    (inventory : RetirementSecurity.TxInventory locals run.before)
    (pid : PeerId) (packets : List DataPacket)
    (native : (run : WGRunWitness (List SkbId)).Valid (packets.mapM newTxSkb))
    (device : run.before.dev = some d)
    (aligned : Aligned related (pendingAt (.selected takePosition) ledger) packets) :
    let after := assignBatch takePosition history.length ledger
    let events := history ++ [Event.old (.allocated packets run)]
    let held := RetirementSecurity.TxLocalBatch.mk .unpublished pid run.value :: locals
    Staged.Obligations.Step ledger after ∧ Core events after debts run.after ∧
      pendingAt (.selected takePosition) after = [] ∧
      RetirementSecurity.TxCoverage held run.after ∧ RetirementSecurity.TxInventory held run.after := by
  obtain ⟨step,valid,resident,mixed,covered,cleanup,ownership,inventory⟩ :=
    allocate_mixed_covered before.valid before.physical.resident before.physical.mixed
      before.physical.covered before.physical.cleanup bounded ownership inventory pid packets native device aligned
  have epoch := (ProjectedAction.iff_run_ambient _ _ _).mp (allocate_epoch packets)
    run.before run.ambientBefore run.value run.after run.ambientAfter native
  have queues := (ProjectedAction.iff_run_ambient _ _ _).mp (allocate_staged packets)
    run.before run.ambientBefore run.value run.after run.ambientAfter native
  refine ⟨step,⟨?_,(before.queues.assigned _ _).views_append _ epoch queues,
    (before.selected.assigned _ _).append _,⟨resident,covered,cleanup,mixed⟩⟩,
    assignBatch_selected_empty _ _ _,ownership,inventory⟩
  rw [births_quiet _ rfl]
  exact valid

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
