import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverScheduler

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Origins Origins.Retaining

theorem carrier_delete_timer (pid : PeerId) (timer : PeerTimer) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (delTimer pid timer) :=
  carrier_frame confirmed (ConfiguredIdentity.delTimer_view pid timer)
    (delTimer_native pid timer confirmed)

theorem carrier_modify_timer (site : HiddenSite) (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (modPeerTimer site pid timer delay) :=
  carrier_frame confirmed (ConfiguredIdentity.modPeerTimer_view site pid timer delay)
    (modTimer_native site pid timer delay confirmed)

theorem carrier_queued (pid : PeerId) (retry : Bool) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (sendQueuedHandshakeInitiation pid retry) :=
  carrier_join confirmed (ConfiguredTraffic.queued pid retry) (queued_native pid retry confirmed)

theorem carrier_clear_endpoint (pid : PeerId) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (clearPeerEndpointSrc pid) :=
  carrier_frame confirmed
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentDeferred.«0».Leanux.Proofs.WG.CurrentDeferred.clearEndpoint_view) pid)
    (clearEndpoint_native pid confirmed)

theorem carrier_purge (pid : PeerId) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (purgeStagedPackets pid) :=
  carrier_frame confirmed
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentDeferred.«0».Leanux.Proofs.WG.CurrentDeferred.purge_view) pid)
    (purge_native pid confirmed)

macro "responder_carrier_timer_step " confirmed:term : tactic => `(tactic| first
  | (rx_retention_head clearPeerEndpointSrc; exact carrier_clear_endpoint _ $confirmed)
  | (rx_retention_head purgeStagedPackets; exact carrier_purge _ $confirmed)
  | (rx_retention_head sendQueuedHandshakeInitiation; exact carrier_queued _ _ $confirmed)
  | (rx_retention_head peerGet; exact carrier_peer_get _ $confirmed)
  | (rx_retention_head delTimer; exact carrier_delete_timer _ _ $confirmed)
  | (rx_retention_head modPeerTimer; exact carrier_modify_timer _ _ _ _ $confirmed)
  | responder_carrier_handshake_step $confirmed)

theorem carrier_retransmit (pid : PeerId) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (expiredRetransmitHandshake pid) := by
  unfold expiredRetransmitHandshake
  simp (config := {zeta := false}) only
    [branch,branchCmp,Functor.discard,map_const,Function.comp_def,map_eq_pure_bind]
  repeat' responder_carrier_timer_step confirmed

theorem carrier_new_handshake (pid : PeerId) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (expiredNewHandshake pid) :=
  preserves_bind (carrier_clear_endpoint pid confirmed) (fun _ => carrier_queued pid false confirmed)

theorem carrier_zero_material (pid : PeerId) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (expiredZeroKeyMaterial pid) := by
  unfold expiredZeroKeyMaterial
  simp (config := {zeta := false}) only [branch,peekQueuedUnit,recordQueued]
  repeat' responder_carrier_timer_step confirmed

theorem carrier_clear_worker (H1 : H1ResponderCurrentEdges) (pid : PeerId) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (queuedExpiredZeroKeyMaterial pid) :=
  carrier_join confirmed (ConfiguredRemoval.queuedClear pid) (clearWorker_native H1 pid confirmed)

theorem carrier_send_worker (pid : PeerId) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (handshakeSendWorker pid) :=
  carrier_join confirmed (ConfiguredRemoval.handshakeWorker pid) (sendWorker_native pid confirmed)

end Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
