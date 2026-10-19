import Leanux.Proofs.WG.TransmitSecurity.StagedPeerCreationFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedDeferredFrames
import Leanux.Proofs.Framing.WGConfiguration
import Leanux.Proofs.Framing.WGSocketLifecycle

/-! Configuration metadata and socket updates preserve every staged origin.
The projection retains device epoch, peer allocation and ordered plaintexts. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins.Native
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem configuration {action : WG.M α} (same : SameConfiguration action) :
    Preserves (Inv h) action := by
  apply frame
  · exact same.of_factor (fun s => s.dev.map Device.ifindex) Packets.epoch
      (fun _ => by simp only [configurationView,configurationDevice,wgOwnedView,wgStoreView,
        Packets.epoch,Option.map_map,Function.comp_def])
  · apply Staged.of_view
    exact same.of_factor (fun s => stagedAt {dev := s.dev}) stagedAt
      (fun w => by funext pid; simp only [configurationView,configurationDevice,wgOwnedView,
        wgStoreView,stagedAt,Option.bind_map,Function.comp_def])

theorem socket {action : WG.M α} (same : SameSocket action) :
    Preserves (Inv h) action := by
  apply frame
  · exact same.of_factor (fun s => s.dev.map Device.ifindex) Packets.epoch
      (fun _ => by simp only [socketView,socketDevice,wgOwnedView,wgStoreView,
        Packets.epoch,Option.map_map,Function.comp_def])
  · apply Staged.of_view
    exact same.of_factor (fun s => stagedAt {dev := s.dev}) stagedAt
      (fun w => by funext pid; simp only [socketView,socketDevice,wgOwnedView,
        wgStoreView,stagedAt,Option.bind_map,Function.comp_def])

theorem public_lookup (key : Key) : Preserves (Inv h) (pubkeyLookup key) :=
  frame (epoch_rx_ring (RxRing.pubkeyLookup_cell key)) (Staged.pubkey_lookup key)

theorem expire_keys (pid : PeerId) : Preserves (Inv h) (expireCurrentPeerKeypairs pid) := by
  unfold expireCurrentPeerKeypairs
  simp only [requireNotPending,pure_bind]
  repeat' first
    | (rx_retention_head handshakeClear; exact native_clear_handshake _)
    | (rx_retention_head resetLastSentHandshake; exact reset_handshake _)
    | (rx_retention_head setKeypair; exact write_key _ _)
    | staged_origin_native

theorem set_port (port : Nat) : Preserves (Inv h) (setPort port) := by
  unfold setPort
  repeat' first
    | (rx_retention_head clearPeerEndpointSrc; exact clear_endpoint _)
    | (rx_retention_head socketInit; exact socket (socketInit_sameSocket _))
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Inv h)
       intro x b
       change Preserves (Inv h) _)
    | staged_origin_native

theorem keepalive_decision (p : Peer) (interval : Nat) (running : Bool) : SameWGStore
    (WG.andM (branch .peerKeepaliveWasZero (p.persistentKeepaliveInterval == 0))
      (WG.andM (branch .peerKeepaliveNonzero (interval != 0)) (branch .peerKeepaliveRunning running))) := by
  intro initial
  change Preserves (fun w => wgStoreView w = initial) _
  unfold WG.andM
  simp only [branch]
  repeat' first
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins.Native
