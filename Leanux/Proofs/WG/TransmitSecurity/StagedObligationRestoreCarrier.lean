import Leanux.Proofs.WG.TransmitSecurity.StagedObligationCarrier
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationRestoreMaterialFrames

/-! Restoration joins queue accounting, canonical births and allocated cleanup
coverage. The selected plaintext alignment remains an actual caller-local
entry obligation supplied by the preceding take and native nonce loop. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
open Leanux Leanux.WG Staged.Origins
open AuthenticatedEffects CausalJournal AllocatedObligation

theorem core_restore (r : HandshakeSecurity.StagedConservation.Restore.Receipt)
    (native : r.Valid) (before : Core history ledger debts r.run.before)
    (epoch : Packets.epoch r.run.before = some generation)
    (resident : stagedAt r.run.before r.pid = some (allocation,[])) (position : Nat)
    (held : Aligned (Born history generation r.pid allocation)
      (pendingAt (.selected position) ledger) r.packets) :
    let after := transferLocation (.selected position) (.staged generation r.pid allocation) ledger
    Step ledger after ∧ Core (history ++ [.stagedRestored r]) after debts r.run.after ∧
      pendingAt (.selected position) after = [] ∧
      pendingAt (.staged generation r.pid allocation) after = pendingAt (.selected position) ledger := by
  dsimp only
  obtain ⟨step,valid,queues,empty,located⟩ :=
    restore_empty_step r native before.valid before.queues epoch resident position held
  have views := restore_material_views r native
  refine ⟨step,⟨?_,queues.append_history _,(before.selected.restored position generation r.pid allocation).append _,
    ((before.physical.ledger_frame (restore_allocated_frame _ _ _ _)).views views.1 views.2).append _⟩,
    empty,located⟩
  rw [births_quiet _ rfl]
  exact valid

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
