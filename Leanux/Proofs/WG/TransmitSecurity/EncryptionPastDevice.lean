import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastDeviceFrames

/-! Native device open/up and destruction preserve the same historical exclusion.
Deletion callbacks remain explicit at their original source positions. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.DeviceLifecycle
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues
open TxDisposition Keys Socket Maintenance Removal
set_option maxHeartbeats 600000

theorem device_open : Preserves (Ready past active) wgOpen := by
  unfold wgOpen
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head socketInit; exact DeviceFrames.socket (socketInit_sameSocket _))
    | (rx_retention_head sendStagedPackets; exact send _)
    | encryption_past_handshake_step

theorem device_up : Preserves (Ready past active) wgUp := by
  unfold wgUp
  repeat' first
    | (rx_retention_head wgOpen; exact device_open)
    | encryption_past_handshake_step

theorem device_destruct : Preserves (Ready past active) wgDestruct := by
  unfold wgDestruct
  simp (config := {zeta := false}) only [unsupported,invariant]
  repeat' first
    | (rx_retention_head socketReinit; exact socket_reinit _ _)
    | (rx_retention_head peerRemoveAll; exact remove_all)
    | (rx_retention_head mayHaveSlept; exact ready_store mayHaveSlept_sameWGStore)
    | (rx_retention_head ratelimiterUninit; exact DeviceFrames.limiter ratelimiterUninit_sameRatelimiter)
    | (rx_retention_head _root_.modify; apply hoare_modify; intro w before; exact DeviceFrames.absent before)
    | (rx_retention_head retireDeviceUnits; exact ready_store retireDeviceUnits_sameWGStore)
    | encryption_past_handshake_step

/-- The source callbacks are actual native actions, unrestricted except for
the explicit preservation facts needed at each invocation. -/
theorem device_delete (onDown onUnregister : WG.M Unit)
    (downRule : Preserves (Ready past active) onDown) (unregisterRule : Preserves (Ready past active) onUnregister) :
    Preserves (Ready past active) (wgDelete onDown onUnregister) := by
  unfold wgDelete
  simp (config := {zeta := false}) only [getWG,monadLift_self,skipCut]
  repeat' first
    | exact downRule
    | exact unregisterRule
    | (rx_retention_head wgDown; exact down)
    | (rx_retention_head wgDestruct; exact device_destruct)
    | (rx_retention_head mayHaveSlept; exact ready_store mayHaveSlept_sameWGStore)
    | encryption_past_handshake_step

theorem device_delete_default : Preserves (Ready past active) (wgDelete : WG.M Int) :=
  device_delete _ _ (preserves_pure ()) (preserves_pure ())


end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.DeviceLifecycle
