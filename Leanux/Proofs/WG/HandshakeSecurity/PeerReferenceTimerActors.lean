import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceScheduler

/-! Deferred timer actors and original send workers preserve positive peer counts. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem saved_device (p : Peer) (f : Device → Device) (same : ∀ d, (f d).peers = d.peers) :
    Framing.Preserves (fun w => Inv w ∧ 0 < p.refcount) (modifyDev f) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (modify_device f same) w a result v b before.1 run,before.2⟩

theorem purge (pid : PeerId)  :
    Framing.Preserves (Inv) (purgeStagedPackets pid) := by
  unfold purgeStagedPackets
  apply hoare_bind _ _ (read_saved pid)
  intro p
  apply hoare_bind _ _ (saved_device p
    (fun d => {d with txDropped := d.txDropped + p.staged.length}) (fun _ => rfl))
  intro _
  exact write_saved pid p (fun current => {current with staged := []}) (fun _ => rfl)

theorem cache_reset_now (pid : PeerId)  :
    Framing.Preserves (Inv) (dstCacheResetNow pid) := by
  unfold dstCacheResetNow
  apply preserves_bind (cache_reset pid)
  intro _
  exact update_peer pid (fun p => {p with dstCache := {p.dstCache with slot := none}})
    (fun _ positive => positive)

theorem clear_endpoint (pid : PeerId)  :
    Framing.Preserves (Inv) (clearPeerEndpointSrc pid) := by
  unfold clearPeerEndpointSrc
  repeat' first
    | (rx_retention_head dstCacheResetNow; exact cache_reset_now _)
    | peer_reference_timer_step

macro "peer_reference_timer_actor_step" : tactic => `(tactic| first
  | (rx_retention_head clearPeerEndpointSrc; exact clear_endpoint _ )
  | (rx_retention_head purgeStagedPackets; exact purge _ )
  | (rx_retention_head sendQueuedHandshakeInitiation; exact queued _ _ )
  | peer_reference_timer_step)

theorem retransmit (pid : PeerId)  :
    Framing.Preserves (Inv) (expiredRetransmitHandshake pid) := by
  unfold expiredRetransmitHandshake
  simp (config := {zeta := false}) only
    [branch,branchCmp,Functor.discard,map_const,Function.comp_def,map_eq_pure_bind]
  repeat' peer_reference_timer_actor_step

theorem new_handshake (pid : PeerId)  :
    Framing.Preserves (Inv) (expiredNewHandshake pid) :=
  preserves_bind (clear_endpoint pid) (fun _ => queued pid false)

theorem zero_material (pid : PeerId)  :
    Framing.Preserves (Inv) (expiredZeroKeyMaterial pid) := by
  unfold expiredZeroKeyMaterial
  simp (config := {zeta := false}) only [branch,peekQueuedUnit,recordQueued]
  repeat' peer_reference_timer_actor_step

theorem clear_worker (pid : PeerId)  :
    Framing.Preserves (Inv) (queuedExpiredZeroKeyMaterial pid) :=
  preserves_bind (clear pid) (fun _ =>
    preserves_bind (clear_keys pid) (fun _ => peer_put (some pid)))

theorem send_initiation (pid : PeerId)  :
    Framing.Preserves (Inv) (sendHandshakeInitiation pid) := by
  unfold sendHandshakeInitiation
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head createInitiation; exact create_initiation _)
    | (rx_retention_head addMacToPacket; exact mac _ _)
    | (rx_retention_head sendBufferToPeer; exact send_buffer _ _)
    | (rx_retention_head timersTraversal; exact traversal _)
    | (rx_retention_head timersAnyAuthenticatedPacketSent; exact sent _)
    | (rx_retention_head timersHandshakeInitiated; exact initiated _)
    | peer_reference_timer_actor_step

theorem send_worker (pid : PeerId)  :
    Framing.Preserves (Inv) (handshakeSendWorker pid) :=
  preserves_bind (send_initiation pid) (fun _ => peer_put (some pid))

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
