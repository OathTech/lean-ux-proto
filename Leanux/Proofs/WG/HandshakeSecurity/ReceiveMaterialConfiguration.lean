import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialTraffic
import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialConfigurationFrames

/-! Peer/device configuration and opening a device transport allocation
origins through the same observed staging and keepalive callbacks. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Execution
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity Configuration Driver ConfigurationFrames Responder
set_option maxHeartbeats 600000
set_option pp.structureInstances false

private theorem config_forIn {α β : Type} (xs : List α) (init : β) (f : α → β → WGPrefix Journal.Event (ForInStep β))
    (hf : ∀ x b, StatePrefixPreserves (fun h w _ => Carrier h w) Safe (f x b)) : StateSafe (forIn xs init f) :=
  StatePrefixEnsures.forInInvariant xs init f (fun _ h w _ => Carrier h w) Safe
    (fun _ _ _ _ hi => hi.2) hf

private theorem config_bind {g : WGPrefix Journal.Event α} {f : α → WGPrefix Journal.Event β}
    (hg : StatePrefixPreserves (fun h w _ => Carrier h w) Safe g)
    (hf : ∀ x, StatePrefixPreserves (fun h w _ => Carrier h w) Safe (f x)) :
    StatePrefixPreserves (fun h w _ => Carrier h w) Safe (g >>= f) := StatePrefixEnsures.bind hg hf

theorem config_store {action : WG.M α} (same : SameWGStore action) : StateSafe (liftWGPrefix action) :=
  state_native _ (fun _ => bounded_store same)

private theorem guard_andM (d e : Decision) (b c : Bool) :
    StateSafe (liftWGPrefix (WG.andM (branch d b) (branch e c))) := by
  apply state_native
  intro h
  unfold WG.andM
  simp only [branch]
  repeat' receive_bounded_native_step

private theorem guard_orM (d e : Decision) (b c : Bool) :
    StateSafe (liftWGPrefix (WG.orM (branch d b) (branch e c))) := by
  apply state_native
  intro h
  unfold WG.orM
  simp only [branch]
  repeat' receive_bounded_native_step

macro "receive_config_step" : tactic => `(tactic| first
  | (nonce_source_head Hooks.peerRelease
     change StateSafe (liftWGPrefix _)
     apply state_native
     intro h; repeat' receive_configuration_frame; done)
  | origin_carrier_join_let
  | origin_carrier_join_use
  | (nonce_source_head WG.andM; exact guard_andM _ _ _ _)
  | (nonce_source_head WG.orM; exact guard_orM _ _ _ _)
  | (nonce_source_head peerGet; exact state_native _ (fun _ => ConfigurationFrames.peer_get _))
  | (nonce_source_head setPeerEndpoint; exact state_native _ (fun _ => bounded_endpoint _ _))
  | (resident_native_lift
     apply state_native
     intro h; repeat' receive_configuration_frame; done)
  | (nonce_source_head Pure.pure; exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.2) (fun _ _ _ hi => hi))
  | (nonce_source_head ForIn.forIn; apply config_forIn)
  | (nonce_source_head Bind.bind; apply config_bind)
  | maintenance_intro
  | origin_carrier_reduce
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

theorem configOut_safe (attrs : PeerAttrs) (peer : Option PeerId) (ret : Int) :
    StateSafe (configOut Journal.hooks attrs peer ret) := by
  change StatePrefixPreserves (fun h w _ => Carrier h w) Safe _
  unfold configOut
  repeat' receive_config_step

private theorem finish_end (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId)
    (ret : Int) (running : Bool) : StateSafe (do
      if ← liftWGPrefix (branch .peerRunning running) then Driver.stagingObserved Journal.hooks pid
      Driver.configOut Journal.hooks a peer ret) := by
  apply StatePrefixEnsures.bind (state_ambient _)
  intro active
  split
  · exact StatePrefixEnsures.bind (staging pid) (fun _ => configOut_safe a peer ret)
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
    StateSafe (Driver.configTailFinish Journal.hooks a peer pid ret) := by
  unfold Driver.configTailFinish
  rw [show Driver.fixtureOps Journal.hooks = AuthenticatedEffects.FixtureEffects.neutral from rfl,
    AuthenticatedEffects.FixtureEffects.peerFinish_neutral]
  unfold AuthenticatedEffects.FixtureEffects.peerFinishWith
  apply StatePrefixEnsures.bind (config_store getDev_sameWGStore)
  intro d
  apply StatePrefixEnsures.bind (state_ambient _)
  intro keep
  cases keep with
  | false => exact finish_end a peer pid ret d.running
  | true =>
    dsimp only
    apply StatePrefixEnsures.bind (state_native _ (fun _ => bounded_read_peer pid))
    intro p
    apply StatePrefixEnsures.bind (config_store (decide_keepalive p _ d.running))
    intro send
    apply StatePrefixEnsures.bind (state_native _ (fun _ => bounded_set_peer pid {p with persistentKeepaliveInterval := a.keepalive.getD 0}))
    intro _
    apply StatePrefixEnsures.bind (state_ambient _)
    intro now
    cases now with
    | false => exact finish_end a peer pid ret d.running
    | true => exact StatePrefixEnsures.bind (keepalive pid) (fun _ => finish_end a peer pid ret d.running)

theorem configTail_safe (attrs : PeerAttrs)
    (peer : Option PeerId) (pid : PeerId) :
    StateSafe (configTail Journal.hooks attrs peer pid) := by
  change StatePrefixPreserves (fun h w _ => Carrier h w) Safe _
  unfold configTail peerAllowedIpsWith
  repeat' first
    | (nonce_source_head configOut; exact configOut_safe _ _ _)
    | (nonce_source_head configTailFinish; exact configTailFinish_safe _ _ _ _)
    | receive_config_step

private def pskSource (pid : PeerId) (psk : Key) : WGPrefix Journal.Event Unit := do
  let p ← liftWGPrefix (getPeer pid)
  liftWGPrefix (setPeer pid {p with presharedKey := psk})

private theorem psk_write (pid : PeerId) (psk : Key) : StateSafe (pskSource pid psk) :=
  StatePrefixEnsures.bind (state_native _ (fun _ => bounded_read_peer pid)) (fun p => state_native _ (fun _ => bounded_set_peer pid {p with presharedKey := psk}))

private theorem update_control (a : PeerAttrs) (flags : UInt32) (psk : Option Key)
    (remove setPsk replace : WGPrefix Journal.Event Unit) (endpoint : Endpoint → WGPrefix Journal.Event Unit)
    (out : Int → WGPrefix Journal.Event Int) (tail : WGPrefix Journal.Event Int)
    (hr : StateSafe remove) (hs : StateSafe setPsk) (hp : StateSafe replace)
    (he : ∀ ep, StateSafe (endpoint ep)) (ho : ∀ ret, StateSafe (out ret)) (ht : StateSafe tail) :
    StateSafe (peerConfigUpdateWith (fun {_} a => liftWGPrefix a)
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
       exact state_ambient _)
    | (nonce_source_head Pure.pure; exact state_pure _)
    | (nonce_source_head Bind.bind; apply StatePrefixEnsures.bind)
    | maintenance_intro
    | maintenance_reduce
    | maintenance_reduce_match
    | split

theorem configUpdate_safe (a : PeerAttrs) (peer : Option PeerId)
    (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    StateSafe (Driver.configUpdate Journal.hooks a peer flags psk pid) := by
  unfold Driver.configUpdate
  rw [Driver.remove_lift Journal.hooks rfl rfl]
  exact update_control a flags psk _ _ _ _ _ _ (state_native _ (fun _ => ConfigurationFrames.remove peer))
    (psk_write pid (psk.getD [])) (state_native _ (fun _ => ConfigurationFrames.remove_ips pid))
    (fun ep => state_native _ (fun _ => bounded_endpoint pid ep)) (configOut_safe a peer) (configTail_safe a peer pid)

theorem configPeer_safe (attrs : PeerAttrs) :
    StateSafe (configPeer Journal.hooks attrs) := by
  change StatePrefixPreserves (fun h w _ => Carrier h w) Safe _
  unfold configPeer setPeerCmdWith peerCommandAcquiredWith
  repeat' first
    | (nonce_source_head configOut; exact configOut_safe _ _ _)
    | (nonce_source_head configUpdate; exact configUpdate_safe _ _ _ _ _)
    | receive_config_step

theorem configPeers_safe (attrs : DeviceAttrs) :
    StateSafe (configPeers Journal.hooks attrs) := by
  change StatePrefixPreserves (fun h w _ => Carrier h w) Safe _
  unfold configPeers devicePeersWith
  repeat' first
    | (nonce_source_head configPeer; exact configPeer_safe _)
    | receive_config_step

theorem configKey_safe (attrs : DeviceAttrs) :
    StateSafe (configKey Journal.hooks attrs) := by
  change StatePrefixPreserves (fun h w _ => Carrier h w) Safe _
  unfold configKey deviceKeyWith
  simp only [Journal.fixture_neutral,AuthenticatedEffects.FixtureEffects.run_neutral]
  simp only [remove_lift Journal.hooks rfl rfl]
  repeat' first
    | (nonce_source_head configPeers; exact configPeers_safe _)
    | (nonce_source_head stagingObserved; exact staging _)
    | receive_config_step

theorem configDeviceUpdate_safe (attrs : DeviceAttrs) (flags : UInt32) :
    StateSafe (configDeviceUpdate Journal.hooks attrs flags) := by
  change StatePrefixPreserves (fun h w _ => Carrier h w) Safe _
  unfold configDeviceUpdate deviceUpdateWith
  simp only [removeAll_lift Journal.hooks rfl rfl]
  repeat' first
    | (nonce_source_head configKey; exact configKey_safe _)
    | receive_config_step

theorem configDevice_safe (attrs : DeviceAttrs) :
    StateSafe (configDevice Journal.hooks attrs) := by
  change StatePrefixPreserves (fun h w _ => Carrier h w) Safe _
  unfold configDevice setDeviceWith
  repeat' first
    | (nonce_source_head configDeviceUpdate; exact configDeviceUpdate_safe _ _)
    | receive_config_step

theorem opened :
    StateSafe (openObserved Journal.hooks) := by
  change StatePrefixPreserves (fun h w _ => Carrier h w) Safe _
  unfold openObserved
  simp only [Journal.fixture_neutral,AuthenticatedEffects.FixtureEffects.open_neutral]
  unfold AuthenticatedEffects.FixtureEffects.openWith
  repeat' first
    | (nonce_source_head stagingObserved; exact staging _)
    | (nonce_source_head keepaliveObserved; exact keepalive _)
    | receive_config_step

theorem up :
    StateSafe (upObserved Journal.hooks) := by
  change StatePrefixPreserves (fun h w _ => Carrier h w) Safe _
  unfold upObserved
  repeat' first
    | (nonce_source_head openObserved; exact opened)
    | receive_config_step


end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Execution
