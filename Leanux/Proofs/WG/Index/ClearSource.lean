import Leanux.Proofs.WG.Index.ClearFrames
import Leanux.Proofs.WG.Index.StagedSource
import Leanux.Proofs.WG.TimerDiscipline.SectionFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- The original immediate handshake unhash, followed by the peer-store reset. -/
theorem handshakeClear_tables (pid : PeerId) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ handshakeClear pid
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hi := indexRemove_tables
  have hz := handshakeZero_tables
  mvcgen [handshakeClear, IndexOwner.peerDeref, IndexOwner.peerWord,
    getPeer, getDev, getK, invariant, unsupported, hi, hz]

/-- Each actual immediate put filters the table. No slot distinctness or static
release budget is needed for preservation on normal return. -/
theorem keypairsClear_tables (pid : PeerId) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ keypairsClear pid
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hw := modifyPeer_tables
  have hp := keypairPut_tables
  mvcgen [keypairsClear, getPeer, getDev, getK, invariant, hw, hp]

theorem queuedExpiredZeroKeyMaterial_tables (pid : PeerId) :
    Ensures (queuedExpiredZeroKeyMaterial pid) (fun w => TablesSafeKernel w.k)
      (fun _ w => TablesSafeKernel w.k) := by
  have hh := handshakeClear_tables
  have hk := keypairsClear_tables
  have hp := peerPut_tables
  rw [ensures_iff]
  mvcgen [queuedExpiredZeroKeyMaterial, hh, hk, hp]

/-- Original named/head selection, actual queue removal and section-wrapped body.
Malformed selection or release states retain the original stopped outcomes. -/
theorem runOneClearWorker_tables : Ensures Env.runOneClearWorker
    (fun w => TablesSafeKernel w.k) (fun _ w => TablesSafeKernel w.k) := by
  have hp := TimerDiscipline.peekUnit_spec_kernel_variant TablesSafeKernel .clearPeerWorker
  have hq := fun pid => modifyClearWorkQueue_tables (fun queue => queue.erase pid)
  have hb := fun pid => TimerDiscipline.runWorker_kernel_contract .clearPeerWorker
    (queuedExpiredZeroKeyMaterial pid) TablesSafeKernel TablesSafeKernel
    ((ensures_iff _ _ _).mp (queuedExpiredZeroKeyMaterial_tables pid))
  rw [ensures_iff]
  mvcgen [Env.runOneClearWorker, getDev, getK, resolveUnit, invariant, hp, hq, hb]

end Leanux.Proofs.WG.Index
