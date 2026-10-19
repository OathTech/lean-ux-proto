import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceDeviceConfig
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeLifecycleFrames

/-! Shutdown and destruction preserve positive-reference entry certificates
through their actual direct and nested send drains. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
variable {E : Type} [EntryFormat E]
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity

theorem limiter : Framing.Preserves Inv ratelimiterUninit := by
  apply frame (ratelimiterUninit_sameRatelimiter.of_factor
    (fun s : WGStoreView => fun pid => (s.dev.bind fun d => d.peers[pid]?).map Peer.refcount)
    PeerReference.view ?_)
  intro w
  rfl

theorem destruct_finish : Framing.Preserves Inv Exchange.destructFinishSource := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b before run
  cases value
  have gone := (pinned_const _private.Leanux.Proofs.WG.Configuration.LifecycleCompletion.«0».Leanux.Proofs.WG.Configuration.destructFinish_none)
    w v a b run
  apply absent
  simpa only [AllowedIps.routingView,Option.map_eq_none_iff] using gone

theorem down_observed : Observed (E := E) (Driver.downObserved EntrySource.hooks (E := E)) := by
  unfold Driver.downObserved SendExchange.downWith SendExchange.stopWith
  repeat' first
    | (nonce_source_head SendExchange.timersStopWith; exact timers_stop_observed _)
    | (nonce_source_head requireNotPending; exact lift _ (preserves_pure _))
    | (nonce_source_head purgeStagedPackets; exact lift _ (purge _))
    | (nonce_source_head handshakeClear; exact lift _ (clear _))
    | (nonce_source_head resetLastSentHandshake; exact lift _ (reset_sent _))
    | (nonce_source_head socketReinit; exact lift _ (socket (socketReinit_sameSocket _ _)))
    | peer_reference_removal_step

theorem destruct_observed : Observed (E := E) (Driver.destructObserved EntrySource.hooks (E := E)) := by
  change Observed (E := E) (Configuration.destructWith liftWGPrefix
    (Driver.removeAllObserved EntrySource.hooks (E := E)) (liftWGPrefix Exchange.destructFinishSource))
  unfold Configuration.destructWith
  repeat' first
    | (nonce_source_head Driver.removeAllObserved; exact remove_all_observed)
    | (nonce_source_head Exchange.destructFinishSource; exact lift _ destruct_finish)
    | (nonce_source_head socketReinit; exact lift _ (socket (socketReinit_sameSocket _ _)))
    | peer_reference_removal_step

private def peer_counts (s : WGStoreView) (pid : PeerId) : Option Nat :=
  (s.dev.bind fun d => d.peers[pid]?).map Peer.refcount

private theorem link_counts (w : WGWorld) : peer_counts (linkView w) = PeerReference.view w := by
  unfold peer_counts PeerReference.view
  simp only [linkView,linkStore,linkDevice,wgStoreView,Option.bind_map,Function.comp_def]

theorem device_create : Framing.Preserves Inv wgCreate := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  have outcome := (hoare_iff_run_ambient _ _ _).mp (wgCreate_endpoint (linkView w))
    w a result v b rfl run
  rcases outcome with same | ⟨_,fresh⟩
  · have counts := congrArg peer_counts same
    rw [link_counts,link_counts] at counts
    change Positive (PeerReference.view v)
    rw [counts]
    exact hi
  · have empty : PeerReference.view v = fun _ => none := by
      rw [←link_counts v,fresh]
      rfl
    intro pid count found
    rw [empty] at found
    cases found

theorem pre_exit : Framing.Preserves Inv netnsPreExit := by
  unfold netnsPreExit
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head socketReinit; exact socket (socketReinit_sameSocket _ _))
    | (rx_retention_head clearPeerEndpointSrc; exact clear_endpoint _)
    | peer_reference_traffic_step

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
