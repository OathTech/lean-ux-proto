import Leanux.Proofs.WG.TransmitSecurity.NonceEntryFrames
import Leanux.Proofs.WG.Origins.RetainingConfiguration

/-! Configuration may clear resident keys but cannot reset a surviving nonce
frontier. Flushes execute their native send/clear workers. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Nonce.Frames
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem peer_create (key : Key) (psk : Option Key) : SameView view (peerCreate key psk) :=
  full (Origins.Retaining.peerCreate_material key psk) (Keypairs.WGFrames.peerCreate_sameSnapshot key psk)

theorem allowedip (pid : PeerId) (ip : AllowedIpAttrs) : SameView view (setAllowedip pid ip) :=
  full (Origins.Retaining.setAllowedip_material pid ip) (Keypairs.WGMore.setAllowedip_sameSnapshot pid ip)

theorem remove_ips (pid : PeerId) : SameView view (removeByPeer pid) :=
  full (Origins.Retaining.removeByPeer_material pid) (Keypairs.WGFrames.removeByPeer_sameSnapshot pid)

theorem free_ips  : SameView view (WG.free) :=
  full (Origins.Retaining.allowedipsFree_material) (Keypairs.WGFrames.free_sameSnapshot)

theorem make_dead (pid : PeerId) : SameView view (peerMakeDead pid) :=
  full (Origins.Retaining.peerMakeDead_material pid) (Keypairs.WGFrames.peerMakeDead_sameSnapshot pid)

theorem precompute (pid : PeerId) : SameView view (precomputeStaticStatic pid) :=
  full (Origins.Retaining.precomputeStaticStatic_material pid) (Keypairs.WGFrames.precomputeStaticStatic_sameSnapshot pid)

theorem port (n : Nat) : SameView view (setPort n) :=
  full (Origins.Retaining.setPort_material n) (Keypairs.WGMore.setPort_sameSnapshot n)

theorem flushed_send (pid : PeerId) (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) (runFlushedSendWork pid) := by
  unfold runFlushedSendWork
  simp (config := {zeta := false}) only [invariant,hidden]
  repeat' first
    | (rx_retention_head handshakeSendWorker; exact native_frame h (send_worker _))
    | nonce_preserves_step h

theorem flushed_clear (pid : PeerId) (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) (runFlushedClearWork pid) := by
  unfold runFlushedClearWork
  simp (config := {zeta := false}) only [hidden]
  repeat' first
    | (rx_retention_head queuedExpiredZeroKeyMaterial; exact clear_worker _ h)
    | nonce_preserves_step h

theorem drain_send (upTo : Option PeerId) (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) (drainHandshakeSendWq upTo) := by
  unfold drainHandshakeSendWq peekUnit resolveUnit
  simp (config := {zeta := false}) only [invariant,getAmbient,Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (rx_retention_head runFlushedSendWork; exact flushed_send _ h)
    | (rx_retention_head runFlushedClearWork; exact flushed_clear _ h)
    | nonce_preserves_step h

theorem timers_stop (pid : PeerId) (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) (timersStop pid) := by
  unfold timersStop
  repeat' first
    | (rx_retention_head drainHandshakeSendWq; exact drain_send _ h)
    | nonce_timer_step h

theorem remove_after (pid : PeerId) (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) (peerRemoveAfterDead pid) := by
  unfold peerRemoveAfterDead
  simp (config := {zeta := false}) only [branch,invariant,unsupported]
  repeat' first
    | (rx_retention_head keypairsClear; exact clear _ h)
    | (rx_retention_head timersStop; exact timers_stop _ h)
    | (rx_retention_head drainHandshakeSendWq; exact drain_send _ h)
    | nonce_preserves_step h

theorem remove_peer (peer : Option PeerId) (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) (peerRemove peer) := by
  unfold peerRemove
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head peerMakeDead; exact native_frame h (make_dead _))
    | (rx_retention_head peerRemoveAfterDead; exact remove_after _ h)
    | nonce_preserves_step h

theorem remove_all (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) peerRemoveAll := by
  unfold peerRemoveAll
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head WG.free; exact native_frame h free_ips)
    | (rx_retention_head peerMakeDead; exact native_frame h (make_dead _))
    | (rx_retention_head peerRemoveAfterDead; exact remove_after _ h)
    | nonce_preserves_step h

theorem static_key (key : Key) : SameView view (setStaticIdentityPrivateKey key) :=
  full (Origins.Retaining.configuration_material (project := id) _
    ((setStaticIdentityPrivateKey_sameConfiguration key).factor WGOwnedView.toWGStoreView))
    (Keypairs.WGFrames.setStaticIdentityPrivateKey_sameSnapshot key)

theorem cookie_keys : SameView view cookiePrecomputeDeviceKeys :=
  full (Origins.Retaining.configuration_material (project := id) _
    (cookiePrecomputeDeviceKeys_sameConfiguration.factor WGOwnedView.toWGStoreView))
    Keypairs.WGFrames.cookiePrecomputeDeviceKeys_sameSnapshot

theorem config_endpoint (pid : PeerId) (e : Endpoint) : SameView view (setPeerEndpoint pid e) :=
  full (Origins.Retaining.setPeerEndpoint_material pid e) (Keypairs.WGFrames.setPeerEndpoint_sameSnapshot pid e)

macro "nonce_config_native " h:term : tactic => `(tactic| first
  | (rx_retention_head peerCreate; exact native_frame $h (peer_create _ _))
  | (rx_retention_head setAllowedip; exact native_frame $h (allowedip _ _))
  | (rx_retention_head removeByPeer; exact native_frame $h (remove_ips _))
  | (rx_retention_head peerRemove; exact remove_peer _ $h)
  | (rx_retention_head peerRemoveAll; exact remove_all $h)
  | (rx_retention_head pubkeyLookup; exact pubkey _ $h)
  | (rx_retention_head precomputeStaticStatic; exact native_frame $h (precompute _))
  | (rx_retention_head setStaticIdentityPrivateKey; exact native_frame $h (static_key _))
  | (rx_retention_head cookiePrecomputeDeviceKeys; exact native_frame $h cookie_keys)
  | (rx_retention_head expireCurrentPeerKeypairs; exact native_frame $h (expire _))
  | (rx_retention_head setPort; exact native_frame $h (port _))
  | (rx_retention_head lookupInterface; exact native_frame $h ((lookupInterface_sameWGWorld _).factor view))
  | (rx_retention_head setPeerEndpoint; exact native_frame $h (config_endpoint _ _))
  | (rx_retention_head WG.andM; unfold WG.andM)
  | (rx_retention_head WG.orM; unfold WG.orM)
  | (rx_retention_head branch; exact native_frame $h (ambient _))
  | (rx_retention_head generatePublic; exact native_frame $h ((generatePublic_sameWGWorld _).factor view))
  | (rx_retention_head invariant; exact native_frame $h (ambient _))
  | nonce_timer_step $h)

end Leanux.Proofs.WG.TransmitSecurity.Nonce.Frames
