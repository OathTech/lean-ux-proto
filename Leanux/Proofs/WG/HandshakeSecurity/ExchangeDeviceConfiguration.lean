import Leanux.Proofs.WG.HandshakeSecurity.ExchangePeerConfiguration
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeConfigurationFrames

/-! Device configuration composes actual peer command and removal observers.
Local fixture scopes are neutral in this projection; queued sends reached by
removal continue to record their completed exchange operations. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Exchange
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity Configuration
set_option maxHeartbeats 600000
set_option pp.structureInstances false

macro "exchange_configuration_step " facts:term " using " config:term : tactic => `(tactic| first
  | (nonce_source_head generatePublic; exact lift _ (fun h => frame_world h _ (generatePublic_sameWGWorld _)))
  | (nonce_source_head setStaticIdentityPrivateKey
     exact lift _ (fun h => configuration_frame h _ (setStaticIdentityPrivateKey_sameConfiguration _)))
  | (nonce_source_head cookiePrecomputeDeviceKeys
     exact lift _ (fun h => configuration_frame h _ cookiePrecomputeDeviceKeys_sameConfiguration))
  | (nonce_source_head precomputeStaticStatic; exact lift_tag _ (($config).precompute _))
  | (nonce_source_head expireCurrentPeerKeypairs; exact lift _ (fun h => frame h _ (($config).expire _)))
  | (nonce_source_head clearPeerEndpointSrc; exact lift_tag _ (($config).clearEndpoint _))
  | (nonce_source_head setPort; exact lift_tag _ (($config).port _))
  | (nonce_source_head Driver.removeObserved; exact remove_checked $facts _)
  | (nonce_source_head Driver.removeAllObserved; exact remove_all_checked $facts)
  | (nonce_source_head pubkeyLookup; exact lift _ (pubkey_lookup _))
  | (nonce_source_head Driver.stagingObserved; exact staging_checked ($facts).data _)
  | (nonce_source_head lookupInterface; exact lift _ (fun h => frame_world h _ (lookupInterface_sameWGWorld _)))
  | (first | nonce_source_head WG.andM | nonce_source_head WG.orM
     apply lift; intro history
     first | unfold WG.andM | unfold WG.orM
     simp only [branch]
     repeat' first
       | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
       | rx_retention_step)
  | exchange_removal_step $facts)

theorem config_peers (facts : H1DriverSourceFacts) (config : H1ConfigurationTagFrames) (attrs : DeviceAttrs) :
    Preserves (Driver.configPeers ExchangeDriver.hooks attrs) := by
  unfold Driver.configPeers devicePeersWith
  repeat' first
    | (nonce_source_head Driver.configPeer; exact config_peer facts config _)
    | exchange_configuration_step facts using config

private theorem config_key_with (facts : H1DriverSourceFacts) (config : H1ConfigurationTagFrames)
    (attrs : DeviceAttrs) (next : WGPrefix Event Int) (safe : Preserves next) :
    Preserves (deviceKeyWith liftWGPrefix (fun key => liftWGPrefix (pubkeyLookup key))
      (fun peer => liftWGPrefix (peerPut peer)) (Driver.removeObserved ExchangeDriver.hooks)
      (fun pid => liftWGPrefix (precomputeStaticStatic pid))
      (fun pid => liftWGPrefix (expireCurrentPeerKeypairs pid))
      (Driver.stagingObserved ExchangeDriver.hooks) next attrs) := by
  unfold deviceKeyWith
  repeat' first
    | exact safe
    | exchange_configuration_step facts using config

theorem config_key (facts : H1DriverSourceFacts) (config : H1ConfigurationTagFrames) (attrs : DeviceAttrs) :
    Preserves (Driver.configKey ExchangeDriver.hooks attrs) := by
  unfold Driver.configKey
  simp only [show Driver.fixtureOps ExchangeDriver.hooks = AuthenticatedEffects.FixtureEffects.neutral from rfl,
    AuthenticatedEffects.FixtureEffects.run_neutral]
  exact config_key_with facts config attrs _ (config_peers facts config attrs)

theorem config_device_update (facts : H1DriverSourceFacts) (config : H1ConfigurationTagFrames)
    (attrs : DeviceAttrs) (flags : UInt32) :
    Preserves (Driver.configDeviceUpdate ExchangeDriver.hooks attrs flags) := by
  unfold Driver.configDeviceUpdate deviceUpdateWith
  repeat' first
    | (nonce_source_head Driver.configKey; exact config_key facts config _)
    | exchange_configuration_step facts using config

theorem config_device (facts : H1DriverSourceFacts) (config : H1ConfigurationTagFrames) (attrs : DeviceAttrs) :
    Preserves (Driver.configDevice ExchangeDriver.hooks attrs) := by
  unfold Driver.configDevice setDeviceWith
  repeat' first
    | (nonce_source_head Driver.configDeviceUpdate; exact config_device_update facts config _ _)
    | exchange_configuration_step facts using config

end Leanux.Proofs.WG.HandshakeSecurity.Exchange
