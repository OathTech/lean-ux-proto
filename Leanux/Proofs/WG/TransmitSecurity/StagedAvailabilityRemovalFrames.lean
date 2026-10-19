import Leanux.Proofs.WG.HandshakeSecurity.StagedAvailableConfiguration

/-! Native removal and configuration leaves retain available staged births. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration
open Driver AuthenticatedEffects AuthenticatedEffects.CausalJournal HandshakeSecurity
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

macro "available_configuration_native" : tactic => `(tactic| first
  | (rx_retention_head setAllowedip; exact Native.allowedip_set _ _)
  | (rx_retention_head removeByPeer; exact Native.allowedip_remove _)
  | (rx_retention_head WG.free; exact Native.allowedip_free)
  | (rx_retention_head peerMakeDead; exact Native.make_dead _)
  | (rx_retention_head keypairsClear; exact native_clear_keys _)
  | (rx_retention_head handshakeClear; exact native_clear_handshake _)
  | (rx_retention_head runFlushedClearWork; exact native_flushed_clear _)
  | (rx_retention_head resetLastSentHandshake; exact Native.reset_handshake _)
  | (rx_retention_head peerCreate; exact Native.peer_create _ _)
  | (rx_retention_head pubkeyLookup; exact Native.public_lookup _)
  | (rx_retention_head precomputeStaticStatic; exact Native.precompute _)
  | (rx_retention_head expireCurrentPeerKeypairs; exact Native.expire_keys _)
  | (rx_retention_head setStaticIdentityPrivateKey; exact Native.configuration (setStaticIdentityPrivateKey_sameConfiguration _))
  | (rx_retention_head cookiePrecomputeDeviceKeys; exact Native.configuration cookiePrecomputeDeviceKeys_sameConfiguration)
  | (rx_retention_head socketInit; exact Native.socket (socketInit_sameSocket _))
  | (rx_retention_head socketReinit; exact Native.socket (socketReinit_sameSocket _ _))
  | (rx_retention_head setPort; exact Native.set_port _)
  | (rx_retention_head clearPeerEndpointSrc; exact Native.clear_endpoint _)
  | (rx_retention_head setPeerEndpoint; exact Native.endpoint _ _)
  | (rx_retention_head delTimer; exact Native.delete_timer _ _)
  | (rx_retention_head purgeStagedPackets; exact Native.purge _)
  | (rx_retention_head lookupInterface; exact Native.store ((lookupInterface_sameWGWorld _).factor wgStoreView))
  | (rx_retention_head generatePublic; exact Native.store ((generatePublic_sameWGWorld _).factor wgStoreView))
  | (first | rx_retention_head throw | rx_retention_head MonadExceptOf.throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a value v b before run
     cases run)
  | (rx_retention_head peekUnit; unfold peekUnit; exact hoare_liftAmbient _ _)
  | (rx_retention_head resolveUnit; unfold resolveUnit; exact hoare_liftAmbient _ _)
  | staged_available_native)

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
