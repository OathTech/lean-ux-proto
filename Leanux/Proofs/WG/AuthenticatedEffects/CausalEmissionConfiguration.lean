import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionRemoval
import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionStaging
import Leanux.Proofs.WG.AuthenticatedEffects.EmissionRoutingFrames

/-! Actual configuration and interface-open paths retain emission accounting
through their real staging, keepalive and direct removal/drain callbacks. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open Configuration TransmitSecurity TransmitSecurity.Driver HandshakeSecurity
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem fixture (trigger : FixtureEffects.Trigger) (body : WGPrefix Event α) (safe : StateSafe body) :
    StateSafe (FixtureEffects.runWith (fixtureOps hooks) trigger body) := by
  unfold FixtureEffects.runWith
  apply state_bind
  · intro w a h hi
    exact ⟨[.scope (.entered ⟨h.length,.fixture trigger⟩)],rfl,True.intro,hi.quiet _ rfl⟩
  · intro token
    exact state_bind safe (fun value => state_bind (state_emit _ rfl) (fun _ => state_pure value))

macro "emission_config_step" : tactic => `(tactic| first
  | (emission_head Hooks.peerRelease; change StateSafe (liftWGPrefix _); apply state_native; exact fun initial => peerPut_sent_spec (· = initial) _)
  | (emission_native_head peerGet; exact state_native _ (peerGet_sent _))
  | (emission_native_head peerCreate; exact state_native _ (EmissionConfiguration.peer_create _ _))
  | (emission_native_head setAllowedip; exact state_native _ (EmissionAllowedIps.allowedip _ _))
  | (emission_native_head removeByPeer; exact state_native _ (EmissionAllowedIps.remove_peer _))
  | (emission_native_head pubkeyLookup; exact state_native _ (fun initial => pubkeyLookup_sent_spec (· = initial) _))
  | (emission_native_head precomputeStaticStatic; exact state_native _ (EmissionConfiguration.precompute _))
  | (emission_native_head setStaticIdentityPrivateKey; exact state_native _ (EmissionConfiguration.static_identity _))
  | (emission_native_head cookiePrecomputeDeviceKeys; exact state_native _ EmissionConfiguration.cookie_keys)
  | (emission_native_head expireCurrentPeerKeypairs; exact state_native _ (EmissionClearing.expire _))
  | (emission_native_head setPort; exact state_native _ (EmissionConfiguration.port _))
  | (emission_native_head socketInit; exact state_native _ (EmissionConfiguration.socket _))
  | (emission_native_head clearPeerEndpointSrc; exact state_native _ (EmissionCleanup.clear_endpoint _))
  | (emission_native_head lookupInterface; exact state_native _ ((lookupInterface_sameWGWorld _).factor WGWorld.sent))
  | (emission_native_head setPeerEndpoint; exact state_native _ (EmissionFrames.endpoint_value _ _))
  | (emission_native_head generatePublic; exact state_native _ ((generatePublic_sameWGWorld _).factor WGWorld.sent))
  | emission_removal_step)

theorem config_out (attrs : PeerAttrs) (peer : Option PeerId) (ret : Int) : StateSafe (configOut hooks attrs peer ret) := by
  unfold configOut
  repeat' emission_config_step

theorem config_tail_finish (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    StateSafe (configTailFinish hooks attrs peer pid ret) := by
  unfold configTailFinish FixtureEffects.peerFinishObserved FixtureEffects.peerFinishWith
  repeat' first
    | (emission_head FixtureEffects.runWith; apply fixture)
    | (emission_head configOut; exact config_out _ _ _)
    | (emission_head stagingObserved; exact staging _)
    | (emission_head keepaliveObserved; exact keepalive _)
    | emission_config_step

theorem config_tail (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) : StateSafe (configTail hooks attrs peer pid) := by
  unfold configTail peerAllowedIpsWith
  repeat' first
    | (emission_head configOut; exact config_out _ _ _)
    | (emission_head configTailFinish; exact config_tail_finish _ _ _ _)
    | emission_config_step

theorem config_update (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    StateSafe (configUpdate hooks attrs peer flags psk pid) := by
  unfold configUpdate peerConfigUpdateWith
  repeat' first
    | (emission_head configOut; exact config_out _ _ _)
    | (emission_head configTail; exact config_tail _ _ _)
    | (emission_head removeObserved; exact remove _)
    | emission_config_step

theorem config_peer (attrs : PeerAttrs) : StateSafe (configPeer hooks attrs) := by
  unfold configPeer setPeerCmdWith peerCommandAcquiredWith
  repeat' first
    | (emission_head configOut; exact config_out _ _ _)
    | (emission_head configUpdate; exact config_update _ _ _ _ _)
    | emission_config_step

theorem config_peers (attrs : DeviceAttrs) : StateSafe (configPeers hooks attrs) := by
  unfold configPeers devicePeersWith
  repeat' first
    | (emission_head configPeer; exact config_peer _)
    | emission_config_step

theorem config_key (attrs : DeviceAttrs) : StateSafe (configKey hooks attrs) := by
  unfold configKey deviceKeyWith
  repeat' first
    | (emission_head FixtureEffects.runWith; apply fixture)
    | (emission_head configPeers; exact config_peers _)
    | (emission_head removeObserved; exact remove _)
    | (emission_head stagingObserved; exact staging _)
    | emission_config_step

theorem config_device_update (attrs : DeviceAttrs) (flags : UInt32) : StateSafe (configDeviceUpdate hooks attrs flags) := by
  unfold configDeviceUpdate deviceUpdateWith
  repeat' first
    | (emission_head configKey; exact config_key _)
    | (emission_head removeAllObserved; exact remove_all)
    | emission_config_step

theorem config_device (attrs : DeviceAttrs) : StateSafe (configDevice hooks attrs) := by
  unfold configDevice setDeviceWith
  repeat' first
    | (emission_head configDeviceUpdate; exact config_device_update _ _)
    | emission_config_step

theorem opened : StateSafe (openObserved hooks) := by
  unfold openObserved FixtureEffects.openObserved FixtureEffects.openWith
  repeat' first
    | (emission_head FixtureEffects.runWith; apply fixture)
    | (emission_head stagingObserved; exact staging _)
    | (emission_head keepaliveObserved; exact keepalive _)
    | emission_config_step

theorem up : StateSafe (upObserved hooks) := by
  unfold upObserved
  repeat' first
    | (emission_head openObserved; exact opened)
    | emission_config_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
