import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveDeviceConfig

/-! Device replacement retains archived peer allocations and their frontier.
A new empty device cannot resurrect a deleted peer's timestamp incarnation. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Origins

theorem stop (history : List TimestampReceipt) : Framing.Preserves (StateInv history) wgStop := by
  unfold wgStop
  simp (config := {zeta := false}) only [branch,unsupported,requireNotPending]
  repeat' first
    | (rx_retention_head purgeStagedPackets; exact purge _ history)
    | (rx_retention_head timersStop; exact stop_timers _ history)
    | (rx_retention_head handshakeClear; exact clear _ history)
    | (rx_retention_head keypairsClear; exact clear_keys _ history)
    | (rx_retention_head resetLastSentHandshake; exact reset_sent _ history)
    | (rx_retention_head socketReinit; exact socket (socketReinit_sameSocket _ _) history)
    | archive_traffic_step history

theorem down (history : List TimestampReceipt) : Framing.Preserves (StateInv history) wgDown := by
  unfold wgDown
  repeat' first
    | (rx_retention_head wgStop; exact stop history)
    | archive_traffic_step history

theorem limiter (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) ratelimiterUninit := by
  apply same_config (ratelimiterUninit_sameRatelimiter.of_factor
    (fun s : WGStoreView =>
      ((fun pid => (s.dev.bind fun d => d.peers[pid]?).map fun p => (p.internalId,p.latestTimestamp)),s.peerCounter))
    configView ?_) history
  intro w
  rfl

theorem destruct (history : List TimestampReceipt) : Framing.Preserves (StateInv history) wgDestruct := by
  unfold wgDestruct
  simp (config := {zeta := false}) only [unsupported,invariant]
  repeat' first
    | (rx_retention_head socketReinit; exact socket (socketReinit_sameSocket _ _) history)
    | (rx_retention_head peerRemoveAll; exact remove_all history)
    | (rx_retention_head mayHaveSlept; exact frame_store history _ mayHaveSlept_sameWGStore)
    | (rx_retention_head ratelimiterUninit; exact limiter history)
    | (rx_retention_head modify
       apply hoare_modify
       intro w hi
       apply state_retained hi
       · intro pid stamp found; cases found
       · exact Nat.le_refl _)
    | (rx_retention_head retireDeviceUnits; exact frame_store history _ retireDeviceUnits_sameWGStore)
    | archive_traffic_step history

private def peer_stamps (s : WGStoreView) (pid : PeerId) : Option (Nat × List UInt8) :=
  (s.dev.bind fun d => d.peers[pid]?).map fun p => (p.internalId,p.latestTimestamp)

private theorem link_stamps (w : WGWorld) : peer_stamps (linkView w) = freshnessAt w := by
  unfold peer_stamps freshnessAt
  simp only [linkView,linkStore,linkDevice,wgStoreView,Option.bind_map,Function.comp_def]

theorem device_create (history : List TimestampReceipt) : Framing.Preserves (StateInv history) wgCreate := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  have outcome := (hoare_iff_run_ambient _ _ _).mp (wgCreate_endpoint (linkView w))
    w a result v b rfl run
  rcases outcome with same | ⟨_,fresh⟩
  · have stamps := congrArg peer_stamps same
    rw [link_stamps,link_stamps] at stamps
    have frontier : v.peerCounter = w.peerCounter := congrArg WGStoreView.peerCounter same
    apply state_retained hi
    · intro pid stamp found; rw [←stamps]; exact found
    · rw [frontier]; exact Nat.le_refl _
  · have empty : freshnessAt v = fun _ => none := by
      rw [←link_stamps v,fresh]
      rfl
    have frontier : v.peerCounter = w.peerCounter := congrArg WGStoreView.peerCounter fresh
    apply state_retained hi
    · intro pid stamp found; rw [empty] at found; cases found
    · rw [frontier]; exact Nat.le_refl _

theorem pre_exit (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) netnsPreExit := by
  unfold netnsPreExit
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head socketReinit; exact socket (socketReinit_sameSocket _ _) history)
    | (rx_retention_head clearPeerEndpointSrc; exact clear_endpoint _ history)
    | archive_traffic_step history

end Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
