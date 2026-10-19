import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialTraffic
import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialConfigurationFrames

/-! Peer/device configuration and opening a device transport allocation
origins through the same observed staging and keepalive callbacks. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity Configuration Driver NativeFrames Responder
set_option maxHeartbeats 600000
set_option pp.structureInstances false

private theorem state_forIn {α β : Type} (xs : List α) (init : β) (f : α → β → WGPrefix Journal.Event (ForInStep β))
    (hf : ∀ x b, StatePrefixPreserves (fun h w _ => Carrier h w) Safe (f x b)) : CarrierSafe (forIn xs init f) :=
  StatePrefixEnsures.forInInvariant xs init f (fun _ h w _ => Carrier h w) Safe
    (fun _ _ _ _ hi => hi.1.2) hf

private theorem config_bind {g : WGPrefix Journal.Event α} {f : α → WGPrefix Journal.Event β}
    (hg : StatePrefixPreserves (fun h w _ => Carrier h w) Safe g)
    (hf : ∀ x, StatePrefixPreserves (fun h w _ => Carrier h w) Safe (f x)) :
    StatePrefixPreserves (fun h w _ => Carrier h w) Safe (g >>= f) := StatePrefixEnsures.bind hg hf

theorem config_store {action : WG.M α} (same : SameWGStore action) : CarrierSafe (liftWGPrefix action) :=
  carrier_lift _ (fun _ => NativeFrames.store same) (bounds_store same)

private theorem guard_andM (d e : Decision) (b c : Bool) :
    CarrierSafe (liftWGPrefix (WG.andM (branch d b) (branch e c))) := by
  apply carrier_lift
  · intro h
    unfold WG.andM
    simp only [branch]
    repeat' resident_poll_frame
  · apply bounds_forget
    intro labels
    unfold WG.andM
    simp only [branch]
    repeat' responder_carrier_poll_step labels

private theorem guard_orM (d e : Decision) (b c : Bool) :
    CarrierSafe (liftWGPrefix (WG.orM (branch d b) (branch e c))) := by
  apply carrier_lift
  · intro h
    unfold WG.orM
    simp only [branch]
    repeat' resident_poll_frame
  · apply bounds_forget
    intro labels
    unfold WG.orM
    simp only [branch]
    repeat' responder_carrier_poll_step labels

macro "resident_config_step" : tactic => `(tactic| first
  | origin_carrier_join_let
  | origin_carrier_join_use
  | (nonce_source_head WG.andM; exact guard_andM _ _ _ _)
  | (nonce_source_head WG.orM; exact guard_orM _ _ _ _)
  | (nonce_source_head peerGet; exact carrier_lift _ (fun _ => NativeFrames.peer_get _) (bounds_peer_get _))
  | (nonce_source_head setPeerEndpoint; exact carrier_lift _ (fun _ => NativeFrames.endpoint _ _) (bounds_endpoint _ _))
  | (resident_native_lift
     apply carrier_lift
     · intro h; repeat' resident_configuration_frame; done
     · resident_configuration_bounds)
  | (nonce_source_head Pure.pure; exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.1.2) (fun _ _ _ hi => hi))
  | (nonce_source_head ForIn.forIn; apply state_forIn)
  | (nonce_source_head Bind.bind; apply config_bind)
  | maintenance_intro
  | origin_carrier_reduce
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

theorem configOut_safe (attrs : PeerAttrs) (peer : Option PeerId) (ret : Int) :
    CarrierSafe (configOut attrs peer ret) := by
  change StatePrefixPreserves (fun h w _ => Carrier h w) Safe _
  unfold configOut
  repeat' resident_config_step

private theorem finish_end (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId)
    (ret : Int) (running : Bool) : CarrierSafe (do
      if ← liftWGPrefix (branch .peerRunning running) then Driver.stagingObserved Journal.hooks pid
      Driver.configOut a peer ret) := by
  apply StatePrefixEnsures.bind (carrier_ambient _)
  intro active
  split
  · exact StatePrefixEnsures.bind (staging_carrier pid) (fun _ => configOut_safe a peer ret)
  · exact configOut_safe a peer ret

private theorem decide_keepalive (p : Peer) (interval : Nat) (running : Bool) : SameWGStore
    (WG.andM (branch .peerKeepaliveWasZero (p.persistentKeepaliveInterval == 0))
      (WG.andM (branch .peerKeepaliveNonzero (interval != 0)) (branch .peerKeepaliveRunning running))) := by
  intro initial
  change Framing.Preserves (fun w => wgStoreView w = initial) _
  unfold WG.andM
  simp only [branch]
  repeat' first
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

theorem configTailFinish_safe (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    CarrierSafe (Driver.configTailFinish Journal.hooks a peer pid ret) := by
  unfold Driver.configTailFinish
  rw [show Driver.fixtureOps Journal.hooks = AuthenticatedEffects.FixtureEffects.neutral from rfl,
    AuthenticatedEffects.FixtureEffects.peerFinish_neutral]
  unfold AuthenticatedEffects.FixtureEffects.peerFinishWith
  apply StatePrefixEnsures.bind (config_store getDev_sameWGStore)
  intro d
  apply StatePrefixEnsures.bind (carrier_ambient _)
  intro keep
  cases keep with
  | false => exact finish_end a peer pid ret d.running
  | true =>
    dsimp only
    apply StatePrefixEnsures.bind (read_saved pid)
    intro p
    apply StatePrefixEnsures.bind (saved_store pid p _ (decide_keepalive p _ d.running))
    intro send
    apply StatePrefixEnsures.bind (write_saved pid p
      (fun p => {p with persistentKeepaliveInterval := a.keepalive.getD 0}) (fun _ => rfl) (fun _ => rfl))
    intro _
    apply StatePrefixEnsures.bind (carrier_ambient _)
    intro now
    cases now with
    | false => exact finish_end a peer pid ret d.running
    | true => exact StatePrefixEnsures.bind (keepalive_carrier pid) (fun _ => finish_end a peer pid ret d.running)

theorem configTail_safe (attrs : PeerAttrs)
    (peer : Option PeerId) (pid : PeerId) :
    CarrierSafe (configTail Journal.hooks attrs peer pid) := by
  change StatePrefixPreserves (fun h w _ => Carrier h w) Safe _
  unfold configTail peerAllowedIpsWith
  repeat' first
    | (nonce_source_head configOut; exact configOut_safe _ _ _)
    | (nonce_source_head configTailFinish; exact configTailFinish_safe _ _ _ _)
    | resident_config_step

private def pskSource (pid : PeerId) (psk : Key) : WGPrefix Journal.Event Unit := do
  let p ← liftWGPrefix (getPeer pid)
  liftWGPrefix (setPeer pid {p with presharedKey := psk})

private theorem psk_write (pid : PeerId) (psk : Key) : CarrierSafe (pskSource pid psk) :=
  StatePrefixEnsures.bind (read_saved pid) (fun p => write_saved pid p
    (fun p => {p with presharedKey := psk}) (fun _ => rfl) (fun _ => rfl))

private theorem update_control (a : PeerAttrs) (flags : UInt32) (psk : Option Key)
    (remove setPsk replace : WGPrefix Journal.Event Unit) (endpoint : Endpoint → WGPrefix Journal.Event Unit)
    (out : Int → WGPrefix Journal.Event Int) (tail : WGPrefix Journal.Event Int)
    (hr : CarrierSafe remove) (hs : CarrierSafe setPsk) (hp : CarrierSafe replace)
    (he : ∀ ep, CarrierSafe (endpoint ep)) (ho : ∀ ret, CarrierSafe (out ret)) (ht : CarrierSafe tail) :
    CarrierSafe (peerConfigUpdateWith (fun {_} a => liftWGPrefix a)
      remove setPsk replace endpoint out tail a flags psk) := by
  change StatePrefixPreserves (fun h w _ => Carrier h w) Safe _
  unfold peerConfigUpdateWith
  unfold StatePrefixPreserves
  cases a.endpoint
  all_goals repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | (responder_config_callback remove; exact hr)
    | (responder_config_callback setPsk; exact hs)
    | (responder_config_callback replace; exact hp)
    | (responder_config_callback endpoint; exact he _)
    | (responder_config_callback out; exact ho _)
    | (responder_config_callback tail; exact ht)
    | (nonce_source_head WG.andM; exact guard_andM _ _ _ _)
    | (first | nonce_source_head branch | nonce_source_head invariant
       exact carrier_ambient _)
    | (nonce_source_head Pure.pure; exact carrier_pure _)
    | (nonce_source_head Bind.bind; apply StatePrefixEnsures.bind)
    | maintenance_intro
    | maintenance_reduce
    | maintenance_reduce_match
    | split

theorem configUpdate_safe (a : PeerAttrs) (peer : Option PeerId)
    (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    CarrierSafe (Driver.configUpdate Journal.hooks a peer flags psk pid) := by
  unfold Driver.configUpdate
  rw [Driver.remove_lift Journal.hooks rfl]
  exact update_control a flags psk _ _ _ _ _ _ (carrier_lift _ (fun _ => NativeFrames.remove peer) (bounds_remove peer))
    (psk_write pid (psk.getD [])) (carrier_lift _ (fun _ => NativeFrames.remove_ips pid) (bounds_forget (DriverCuts.carrier_remove_ips pid)))
    (fun ep => carrier_lift _ (fun _ => NativeFrames.endpoint pid ep) (bounds_endpoint pid ep)) (configOut_safe a peer) (configTail_safe a peer pid)

theorem configPeer_safe (attrs : PeerAttrs) :
    CarrierSafe (configPeer Journal.hooks attrs) := by
  change StatePrefixPreserves (fun h w _ => Carrier h w) Safe _
  unfold configPeer setPeerCmdWith peerCommandAcquiredWith
  repeat' first
    | (nonce_source_head configOut; exact configOut_safe _ _ _)
    | (nonce_source_head configUpdate; exact configUpdate_safe _ _ _ _ _)
    | resident_config_step

theorem configPeers_safe (attrs : DeviceAttrs) :
    CarrierSafe (configPeers Journal.hooks attrs) := by
  change StatePrefixPreserves (fun h w _ => Carrier h w) Safe _
  unfold configPeers devicePeersWith
  repeat' first
    | (nonce_source_head configPeer; exact configPeer_safe _)
    | resident_config_step

theorem configKey_safe (attrs : DeviceAttrs) :
    CarrierSafe (configKey Journal.hooks attrs) := by
  change StatePrefixPreserves (fun h w _ => Carrier h w) Safe _
  unfold configKey deviceKeyWith
  simp only [Journal.fixture_neutral,AuthenticatedEffects.FixtureEffects.run_neutral]
  simp only [remove_lift Journal.hooks rfl]
  repeat' first
    | (nonce_source_head configPeers; exact configPeers_safe _)
    | (nonce_source_head stagingObserved; exact staging_carrier _)
    | resident_config_step

theorem configDeviceUpdate_safe (attrs : DeviceAttrs) (flags : UInt32) :
    CarrierSafe (configDeviceUpdate Journal.hooks attrs flags) := by
  change StatePrefixPreserves (fun h w _ => Carrier h w) Safe _
  unfold configDeviceUpdate deviceUpdateWith
  simp only [removeAll_lift Journal.hooks rfl]
  repeat' first
    | (nonce_source_head configKey; exact configKey_safe _)
    | resident_config_step

theorem configDevice_safe (attrs : DeviceAttrs) :
    CarrierSafe (configDevice Journal.hooks attrs) := by
  change StatePrefixPreserves (fun h w _ => Carrier h w) Safe _
  unfold configDevice setDeviceWith
  repeat' first
    | (nonce_source_head configDeviceUpdate; exact configDeviceUpdate_safe _ _)
    | resident_config_step

theorem opened :
    CarrierSafe (openObserved Journal.hooks) := by
  change StatePrefixPreserves (fun h w _ => Carrier h w) Safe _
  unfold openObserved
  simp only [Journal.fixture_neutral,AuthenticatedEffects.FixtureEffects.open_neutral]
  unfold AuthenticatedEffects.FixtureEffects.openWith
  repeat' first
    | (nonce_source_head stagingObserved; exact staging_carrier _)
    | (nonce_source_head keepaliveObserved; exact keepalive_carrier _)
    | resident_config_step

theorem up :
    CarrierSafe (upObserved Journal.hooks) := by
  change StatePrefixPreserves (fun h w _ => Carrier h w) Safe _
  unfold upObserved
  repeat' first
    | (nonce_source_head openObserved; exact opened)
    | resident_config_step


end Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
