import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveScheduler

/-! Timer and deferred handshake actors preserve the retained-peer archive;
their saved peer copies keep the exact pre-write read witness. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem saved_device (pid : PeerId) (p : Peer) (f : Device → Device)
    (same : ∀ d, (f d).peers = d.peers) (history : List TimestampReceipt) :
    Framing.Preserves (fun w => StateInv history w ∧ Responder.SavedNativePeer pid p w) (modifyDev f) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  have preserved := (hoare_iff_run_ambient _ _ _).mp (modify_device f same history) w a result v b hi.1 run
  cases run
  obtain ⟨d,hd,hp⟩ := hi.2
  refine ⟨preserved,f d,?_,?_⟩
  · simp only [hd,Option.map_some]
  · simpa only [same] using hp

theorem purge (pid : PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (purgeStagedPackets pid) := by
  unfold purgeStagedPackets
  apply hoare_bind _ _ (read_saved pid history)
  intro p
  apply hoare_bind _ _ (saved_device pid p
    (fun d => {d with txDropped := d.txDropped + p.staged.length}) (fun _ => rfl) history)
  intro _
  exact write_saved pid p (fun current => {current with staged := []}) (fun _ => ⟨rfl,rfl⟩) history

theorem cache_reset_now (pid : PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (dstCacheResetNow pid) := by
  unfold dstCacheResetNow
  apply preserves_bind (cache_reset pid history)
  intro _
  exact update_peer pid (fun p => {p with dstCache := {p.dstCache with slot := none}})
    (fun _ => ⟨rfl,rfl⟩) history

theorem clear_endpoint (pid : PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (clearPeerEndpointSrc pid) := by
  unfold clearPeerEndpointSrc
  repeat' first
    | (rx_retention_head dstCacheResetNow; exact cache_reset_now _ history)
    | archive_timer_step history

macro "archive_timer_actor_step " history:term : tactic => `(tactic| first
  | (rx_retention_head clearPeerEndpointSrc; exact clear_endpoint _ $history)
  | (rx_retention_head purgeStagedPackets; exact purge _ $history)
  | (rx_retention_head sendQueuedHandshakeInitiation; exact queued _ _ $history)
  | archive_timer_step $history)

theorem retransmit (pid : PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (expiredRetransmitHandshake pid) := by
  unfold expiredRetransmitHandshake
  simp (config := {zeta := false}) only
    [branch,branchCmp,Functor.discard,map_const,Function.comp_def,map_eq_pure_bind]
  repeat' archive_timer_actor_step history

theorem new_handshake (pid : PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (expiredNewHandshake pid) :=
  preserves_bind (clear_endpoint pid history) (fun _ => queued pid false history)

theorem zero_material (pid : PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (expiredZeroKeyMaterial pid) := by
  unfold expiredZeroKeyMaterial
  simp (config := {zeta := false}) only [branch,peekQueuedUnit,recordQueued]
  repeat' archive_timer_actor_step history

theorem clear_worker (pid : PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (queuedExpiredZeroKeyMaterial pid) :=
  preserves_bind (clear pid history) (fun _ =>
    preserves_bind (clear_keys pid history) (fun _ => peer_put (some pid) history))

theorem send_initiation (pid : PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (sendHandshakeInitiation pid) := by
  unfold sendHandshakeInitiation
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head createInitiation; exact create_initiation _ history)
    | (rx_retention_head addMacToPacket; exact mac _ _ history)
    | (rx_retention_head sendBufferToPeer; exact send_buffer _ _ history)
    | (rx_retention_head timersTraversal; exact traversal _ history)
    | (rx_retention_head timersAnyAuthenticatedPacketSent; exact sent _ history)
    | (rx_retention_head timersHandshakeInitiated; exact initiated _ history)
    | archive_timer_actor_step history

theorem send_worker (pid : PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (handshakeSendWorker pid) :=
  preserves_bind (send_initiation pid history) (fun _ => peer_put (some pid) history)

end Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
