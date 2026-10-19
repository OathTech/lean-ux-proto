import Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertextNativeReadyFrames

/-! All five native timer callbacks retain the same physical and ready
batch carrier; keepalive callbacks use the full native staging proof. -/
namespace Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext.Native
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity Queues.RxCredits

theorem clear_endpoint (pid : PeerId) : Preserves (Coherent locals active) (clearPeerEndpointSrc pid) := by
  unfold clearPeerEndpointSrc dstCacheResetNow
  repeat' first
    | (rx_retention_head dstCacheReset; exact maintenance_coherent (.cache _))
    | ready_ciphertext_coherent_step

theorem purge (pid : PeerId) : Preserves (Coherent locals active) (purgeStagedPackets pid) := by
  apply coherent_join (OccurrenceTimers.purge pid)
  apply wire
  · intro initial
    change Preserves (fun w => handoffTxView w = initial) _
    unfold purgeStagedPackets
    repeat' crypt_queue_step initial
  · intro initial
    change Preserves (fun w => txCryptWire w = initial) _
    unfold purgeStagedPackets
    repeat' crypt_wire_step initial


theorem peer_get_coherent (pid : PeerId) : Preserves (Coherent locals active) (peerGet pid) :=
  coherent_join (OccurrenceTimers.peer_get pid) (peer_get pid)

macro "batch_timer_step" : tactic => `(tactic| first
  | (rx_retention_head delTimer; exact maintenance_coherent (.deleteTimer _ _))
  | (rx_retention_head modPeerTimer; exact maintenance_coherent (.modifyTimer _ _ _ _))
  | (rx_retention_head sendKeepalive; exact keepalive _)
  | (rx_retention_head sendQueuedHandshakeInitiation; exact maintenance_coherent (.queuedHandshake _ _))
  | (rx_retention_head clearPeerEndpointSrc; exact clear_endpoint _)
  | (rx_retention_head purgeStagedPackets; exact purge _)
  | (rx_retention_head peerGet; exact peer_get_coherent _)
  | (rx_retention_head peerPut; exact coherent_join (RxPollOccurrences.peer_put _) (peer_put _))
  | ready_ciphertext_coherent_step)

theorem callback (pid : PeerId) (timer : PeerTimer) :
    Preserves (Coherent locals active) (timerCallback pid timer) := by
  cases timer with
  | retransmitHandshake =>
    change Preserves (Coherent locals active) (expiredRetransmitHandshake pid)
    unfold expiredRetransmitHandshake
    simp (config := {zeta := false}) only [branch,branchCmp,Functor.discard,map_const,
      Function.comp_apply,Function.const,map_eq_pure_bind]
    repeat' batch_timer_step
  | sendKeepalive =>
    change Preserves (Coherent locals active) (expiredSendKeepalive pid)
    unfold expiredSendKeepalive
    simp (config := {zeta := false}) only [branch,Functor.discard,map_const,
      Function.comp_apply,Function.const,map_eq_pure_bind]
    repeat' batch_timer_step
  | newHandshake =>
    change Preserves (Coherent locals active) (expiredNewHandshake pid)
    unfold expiredNewHandshake
    repeat' batch_timer_step
  | zeroKeyMaterial =>
    change Preserves (Coherent locals active) (expiredZeroKeyMaterial pid)
    unfold expiredZeroKeyMaterial
    simp (config := {zeta := false}) only [branch,peekQueuedUnit,recordQueued]
    repeat' batch_timer_step
  | persistentKeepalive =>
    change Preserves (Coherent locals active) (expiredSendPersistentKeepalive pid)
    unfold expiredSendPersistentKeepalive
    simp (config := {zeta := false}) only [branch]
    repeat' batch_timer_step


end Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext.Native
