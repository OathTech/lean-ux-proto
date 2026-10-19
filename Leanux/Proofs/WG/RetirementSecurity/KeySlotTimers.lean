import Leanux.Proofs.WG.RetirementSecurity.KeySlotReceive

/-! Original timer callbacks and expiration retain the live-slot relation.
Clock or dispatch fairness is not inferred: this is transport through the
callback selected by the native scheduler, including queue refusal. -/
namespace Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem clear_endpoint (pid : PeerId) : Preserves (InvExcept pending) (clearPeerEndpointSrc pid) := by
  unfold clearPeerEndpointSrc dstCacheResetNow
  repeat' first
    | (rx_retention_head dstCacheReset; exact cache_reset _)
    | key_slot_rx_step

theorem purge (pid : PeerId) : Preserves (InvExcept pending) (purgeStagedPackets pid) := by
  unfold purgeStagedPackets
  repeat' key_slot_rx_step

macro "key_slot_timer_step" : tactic => `(tactic| first
  | (rx_retention_head delTimer; exact del_timer _ _)
  | (rx_retention_head modPeerTimer; exact mod_timer _ _ _ _)
  | (rx_retention_head sendKeepalive; exact keepalive _)
  | (rx_retention_head sendQueuedHandshakeInitiation; exact send_queued _ _)
  | (rx_retention_head clearPeerEndpointSrc; exact clear_endpoint _)
  | (rx_retention_head purgeStagedPackets; exact purge _)
  | key_slot_rx_step)

theorem timer (pid : PeerId) (which : PeerTimer) : Preserves (InvExcept pending) (timerCallback pid which) := by
  cases which with
  | retransmitHandshake =>
    change Preserves (InvExcept pending) (expiredRetransmitHandshake pid)
    unfold expiredRetransmitHandshake
    simp (config := {zeta:=false}) only [branch,branchCmp,Functor.discard,map_const,
      Function.comp_apply,Function.const,map_eq_pure_bind]
    repeat' key_slot_timer_step
  | sendKeepalive =>
    change Preserves (InvExcept pending) (expiredSendKeepalive pid)
    unfold expiredSendKeepalive
    simp (config := {zeta:=false}) only [branch,Functor.discard,map_const,
      Function.comp_apply,Function.const,map_eq_pure_bind]
    repeat' key_slot_timer_step
  | newHandshake =>
    change Preserves (InvExcept pending) (expiredNewHandshake pid)
    unfold expiredNewHandshake
    repeat' key_slot_timer_step
  | zeroKeyMaterial =>
    change Preserves (InvExcept pending) (expiredZeroKeyMaterial pid)
    unfold expiredZeroKeyMaterial
    simp (config := {zeta:=false}) only [branch,peekQueuedUnit,recordQueued]
    repeat' key_slot_timer_step
  | persistentKeepalive =>
    change Preserves (InvExcept pending) (expiredSendPersistentKeepalive pid)
    unfold expiredSendPersistentKeepalive
    simp (config := {zeta:=false}) only [branch]
    repeat' key_slot_timer_step

theorem expire (pid : PeerId) : Preserves (InvExcept pending) (expireCurrentPeerKeypairs pid) := by
  unfold expireCurrentPeerKeypairs requireNotPending
  simp (config := {zeta:=false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head handshakeClear; exact handshake_clear _)
    | (rx_retention_head resetLastSentHandshake; exact reset _)
    | key_slot_rx_step

end Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
