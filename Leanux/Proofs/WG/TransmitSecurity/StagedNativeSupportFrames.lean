import Leanux.Proofs.WG.TransmitSecurity.StagedSocketSendFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedEffectsOrigins
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceTimerFrames

namespace Leanux.Proofs.WG.TransmitSecurity.Staged
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem cookie_consume (msg : List UInt8) : Frame (cookieMessageConsume msg) := by
  intro initial
  unfold cookieMessageConsume
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' staged_handshake_step initial

theorem add_mac (pid : PeerId) (msg : List UInt8) : Frame (addMacToPacket pid msg) := by
  intro initial
  unfold addMacToPacket
  let P := fun queues : PeerId → Option (Nat × List Packet) =>
    ∀ q value, queues q = some value → stagedAt initial q = some value
  apply hoare_bind _ _ (Staged.read_saved P pid)
  intro peer
  dsimp only
  apply hoare_bind _ _ (Staged.write_saved P pid {peer with
    lastMac1Sent := blake2s 16 peer.cookieMac1Key (msg.take (msg.length-32)),haveSentMac1 := true})
  intro _
  change Preserves (Retains initial) _
  unfold WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (Retains initial))
    | staged_handshake_step initial

namespace Origins.Native

theorem endpoint (pid : PeerId) (e : Endpoint) : Preserves (Inv h) (setPeerEndpoint pid e) :=
  exact_ring (RxRing.setPeerEndpoint_cell pid e) (Exact.endpoint pid e)

theorem send_buffer (pid : PeerId) (bytes : List UInt8) : Preserves (Inv h) (sendBufferToPeer pid bytes) :=
  exact_ring (RxRing.sendBufferToPeer_cell pid bytes) (Exact.send_buffer pid bytes)

theorem send_skb (pid : PeerId) (bytes : List UInt8) (ds : Nat) :
    Preserves (Inv h) (sendSkbToPeer pid bytes ds) :=
  exact_ring (RxRing.sendSkbToPeer_cell pid bytes ds) (Exact.sendSkbToPeer_staged pid bytes ds)

theorem create_initiation (pid : PeerId) : Preserves (Inv h) (createInitiation pid) :=
  frame (PacketOrigins.epoch_ring ((RetirementSecurity.OccurrenceKeys.create_initiation_wire pid).factor Prod.fst))
    (Staged.create_initiation pid)

theorem create_response (pid : PeerId) : Preserves (Inv h) (createResponse pid) :=
  frame (epoch_rx_ring (RxRing.createResponse_cell pid)) (Staged.create_response pid)

theorem add_mac (pid : PeerId) (msg : List UInt8) : Preserves (Inv h) (addMacToPacket pid msg) :=
  frame (epoch_rx_ring (RxRing.addMacToPacket_cell pid msg)) (Staged.add_mac pid msg)

theorem cookie_consume (msg : List UInt8) : Preserves (Inv h) (cookieMessageConsume msg) :=
  frame (epoch_rx_ring (RxRing.cookieMessageConsume_cell msg)) (Staged.cookie_consume msg)

theorem cookie {action : WG.M α} (same : SameCookie action) : Preserves (Inv h) action := by
  apply frame (epoch_rx_ring (RxRing.cookie_native_frame same))
  apply Staged.of_view
  apply same.of_factor (fun s : WGOwnedView => fun pid =>
    (s.dev.bind fun d => d.peers[pid]?).map fun p => (p.internalId,p.staged)) stagedAt
  intro w
  simp only [cookieView,wgOwnedView,wgStoreView,cookieDevice,Option.bind_map,Function.comp_def]
  rfl

theorem cookie_reply (msg : List UInt8) (src : SkbSource) : Preserves (Inv h) (sendHandshakeCookie msg src) := by
  apply frame (epoch_rx_ring (RxRing.sendHandshakeCookie_cell msg src))
  apply Staged.of_view
  apply (Cookies.sendHandshakeCookie_frame msg src).of_factor
    (fun s : Option Device × Nat × Nat => fun pid =>
      (s.1.bind fun d => d.peers[pid]?).map fun p => (p.internalId,p.staged)) stagedAt
  intro w
  simp only [Cookies.noiseView,Cookies.viewOfStore,Cookies.scrub,wgStoreView,
    Option.bind_map,Function.comp_def]
  rfl

theorem endpoint_from_skb (pid : PeerId) (src : SkbSource) :
    Preserves (Inv h) (setPeerEndpointFromSkb pid src) := by
  unfold setPeerEndpointFromSkb
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head endpointFromSkb; exact store (endpointFromSkb_sameWGStore _))
    | (rx_retention_head setPeerEndpoint; exact endpoint _ _)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

theorem clear_endpoint (pid : PeerId) : Preserves (Inv h) (clearPeerEndpointSrc pid) :=
  frame (PacketOrigins.epoch_ring ((RetirementSecurity.OccurrenceTimers.clear_endpoint_wire pid).factor Prod.fst))
    (Staged.of_view _ (Exact.clear_endpoint pid))

theorem clear_staged (pid : PeerId) (peer : Peer) : Preserves (Inv h) (setPeer pid {peer with staged := []}) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b before run
  cases run
  exact before.clear pid peer

theorem purge (pid : PeerId) : Preserves (Inv h) (purgeStagedPackets pid) := by
  unfold purgeStagedPackets
  apply preserves_bind (read_peer pid)
  intro peer
  apply preserves_bind (modify_device (h := h) (fun d => {d with txDropped := d.txDropped + peer.staged.length})
    (fun _ => rfl) (fun _ => rfl))
  intro _
  exact clear_staged pid peer

theorem initiated (pid : PeerId) : Preserves (Inv h) (timersHandshakeInitiated pid) := by
  unfold timersHandshakeInitiated
  repeat' first
    | (rx_retention_head callerJiffies; exact (callerJiffies_sameWGWorld _).wp (Inv h))
    | (rx_retention_head jitterBelowRekeyTimeout; exact (jitterBelowRekeyTimeout_sameWGWorld _).wp (Inv h))
    | (rx_retention_head modPeerTimerGuard; exact Native.timer_guard _)
    | (rx_retention_head armTimer; exact Native.arm _ _ _ _)
    | rx_retention_step

end Origins.Native
end Leanux.Proofs.WG.TransmitSecurity.Staged
