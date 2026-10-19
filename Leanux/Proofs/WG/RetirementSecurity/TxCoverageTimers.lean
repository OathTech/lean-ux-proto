import Leanux.Proofs.WG.RetirementSecurity.TxCoverageActors

/-! All native timer callbacks preserve ownership coverage of allocated TX
packets. Plaintext purge is distinct; keepalive enters actual staged send. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxCoverageNative
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits
variable {locals : List TxLocalBatch}

theorem clear_endpoint (pid : PeerId) : Preserves (TxCoverage locals) (clearPeerEndpointSrc pid) := by
  unfold clearPeerEndpointSrc dstCacheResetNow
  repeat' first
    | (rx_retention_head dstCacheReset; exact maintenance (.cache _))
    | coverage_native_step

theorem purge (pid : PeerId) : Preserves (TxCoverage locals) (purgeStagedPackets pid) := by
  apply wire
  · intro initial
    change Preserves (fun w => handoffTxView w = initial) _
    unfold purgeStagedPackets
    repeat' crypt_queue_step initial
  · intro initial
    change Preserves (fun w => txCryptWire w = initial) _
    unfold purgeStagedPackets
    repeat' crypt_wire_step initial


macro "coverage_timer_step" : tactic => `(tactic| first
  | (rx_retention_head delTimer; exact maintenance (.deleteTimer _ _))
  | (rx_retention_head modPeerTimer; exact maintenance (.modifyTimer _ _ _ _))
  | (rx_retention_head sendKeepalive; exact keepalive _)
  | (rx_retention_head sendQueuedHandshakeInitiation; exact maintenance (.queuedHandshake _ _))
  | (rx_retention_head clearPeerEndpointSrc; exact clear_endpoint _)
  | (rx_retention_head purgeStagedPackets; exact purge _)
  | (rx_retention_head peerGet; exact peer_get _)
  | (rx_retention_head peerPut; exact peer_put _)
  | coverage_native_step)

theorem callback (pid : PeerId) (timer : PeerTimer) :
    Preserves (TxCoverage locals) (timerCallback pid timer) := by
  cases timer with
  | retransmitHandshake =>
    change Preserves (TxCoverage locals) (expiredRetransmitHandshake pid)
    unfold expiredRetransmitHandshake
    simp (config := {zeta := false}) only [branch,branchCmp,Functor.discard,map_const,
      Function.comp_apply,Function.const,map_eq_pure_bind]
    repeat' coverage_timer_step
  | sendKeepalive =>
    change Preserves (TxCoverage locals) (expiredSendKeepalive pid)
    unfold expiredSendKeepalive
    simp (config := {zeta := false}) only [branch,Functor.discard,map_const,
      Function.comp_apply,Function.const,map_eq_pure_bind]
    repeat' coverage_timer_step
  | newHandshake =>
    change Preserves (TxCoverage locals) (expiredNewHandshake pid)
    unfold expiredNewHandshake
    repeat' coverage_timer_step
  | zeroKeyMaterial =>
    change Preserves (TxCoverage locals) (expiredZeroKeyMaterial pid)
    unfold expiredZeroKeyMaterial
    simp (config := {zeta := false}) only [branch,peekQueuedUnit,recordQueued]
    repeat' coverage_timer_step
  | persistentKeepalive =>
    change Preserves (TxCoverage locals) (expiredSendPersistentKeepalive pid)
    unfold expiredSendPersistentKeepalive
    simp (config := {zeta := false}) only [branch]
    repeat' coverage_timer_step


end Leanux.Proofs.WG.RetirementSecurity.TxCoverageNative
