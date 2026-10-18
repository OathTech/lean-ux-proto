import Leanux.Proofs.WG.TransmitSecurity.NonceConfigurationFrames
import Leanux.Proofs.WG.Queues.JointDevice

/-! Exact configuration observers expose the keepalive/staging callbacks that
allocate nonces; all remaining native operations retain their original order. -/
set_option maxHeartbeats 600000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TransmitSecurity.Nonce
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration

def configOut (a : PeerAttrs) (peer : Option PeerId) (ret : Int) : WGPrefix Allocation Int := do
  liftWGPrefix (peerPut peer)
  _ ← liftWGPrefix (branch .peerZeroPsk a.presharedKey.isSome)
  pure ret

def configTailFinish (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) : WGPrefix Allocation Int := do
  let running := (← liftWGPrefix getDev).running
  if ← liftWGPrefix (branch .peerHasKeepalive a.keepalive.isSome) then
    let interval := a.keepalive.getD 0
    let p ← liftWGPrefix (getPeer pid)
    let send ← liftWGPrefix (WG.andM (branch .peerKeepaliveWasZero (p.persistentKeepaliveInterval == 0))
      (WG.andM (branch .peerKeepaliveNonzero (interval != 0)) (branch .peerKeepaliveRunning running)))
    liftWGPrefix (setPeer pid {p with persistentKeepaliveInterval := interval})
    if ← liftWGPrefix (branch .peerSendKeepalive send) then keepaliveObserved pid
  if ← liftWGPrefix (branch .peerRunning running) then stagingObserved pid
  configOut a peer ret

def configTail (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) : WGPrefix Allocation Int :=
  peerAllowedIpsWith (fun d b => liftWGPrefix (branch d b))
    (fun ip => liftWGPrefix (setAllowedip pid ip)) (configOut a peer) a (configTailFinish a peer pid)

def configUpdate (a : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) : WGPrefix Allocation Int :=
  peerConfigUpdateWith (fun {_} a => liftWGPrefix a) (liftWGPrefix (peerRemove peer))
    (do let p ← liftWGPrefix (getPeer pid); liftWGPrefix (setPeer pid {p with presharedKey := psk.getD []}))
    (liftWGPrefix (removeByPeer pid)) (fun e => liftWGPrefix (setPeerEndpoint pid e))
    (configOut a peer) (configTail a peer pid) a flags psk

def configPeer (a : PeerAttrs) : WGPrefix Allocation Int :=
  setPeerCmdWith (fun {_} a => liftWGPrefix a) (fun key => liftWGPrefix (pubkeyLookup key))
    (configOut a none)
    (peerCommandAcquiredWith (fun {_} a => liftWGPrefix a)
      (fun key psk => liftWGPrefix (peerCreate key psk)) (fun pid => liftWGPrefix (peerGet pid))
      (configOut a none) (configUpdate a)) a

def configPeers (a : DeviceAttrs) : WGPrefix Allocation Int :=
  devicePeersWith (fun {_} a => liftWGPrefix a) configPeer a

def configKey (a : DeviceAttrs) : WGPrefix Allocation Int :=
  deviceKeyWith (fun {_} a => liftWGPrefix a) (fun key => liftWGPrefix (pubkeyLookup key))
    (fun peer => liftWGPrefix (peerPut peer)) (fun peer => liftWGPrefix (peerRemove peer))
    (fun pid => liftWGPrefix (precomputeStaticStatic pid)) (fun pid => liftWGPrefix (expireCurrentPeerKeypairs pid))
    stagingObserved (configPeers a) a

def configDeviceUpdate (a : DeviceAttrs) (flags : UInt32) : WGPrefix Allocation Int :=
  deviceUpdateWith (fun {_} a => liftWGPrefix a) (fun pid => liftWGPrefix (clearPeerEndpointSrc pid))
    (fun port => liftWGPrefix (setPort port)) (liftWGPrefix peerRemoveAll) (configKey a) a flags

def configDevice (a : DeviceAttrs) : WGPrefix Allocation Int :=
  setDeviceWith (fun {_} a => liftWGPrefix a) (configDeviceUpdate a) a

macro "nonce_config_erasure" : tactic => `(tactic| first
  | (maintenance_head keepaliveObserved; exact keepaliveObserved_erases _)
  | (maintenance_head stagingObserved; exact stagingObserved_erases _)
  | maintenance_intro
  | contradiction
  | maintenance_impossible_match
  | maintenance_erases_join
  | maintenance_erases_join_use
  | maintenance_reduce
  | maintenance_reduce_match
  | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
  | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
  | (maintenance_head ForIn.forIn; apply erasesStatePrefix_forIn)
  | (maintenance_head Bind.bind; apply erasesStatePrefix_bind)
  | (maintenance_head ite; apply erasesStatePrefix_ite)
  | (with_reducible split))

theorem configOut_erases (a : PeerAttrs) (peer : Option PeerId) (ret : Int) :
    ErasesStatePrefix (configOut a peer ret)
      (do peerPut peer; _ ← branch .peerZeroPsk a.presharedKey.isSome; pure ret) := by
  unfold configOut
  repeat' nonce_config_erasure

theorem configTailFinish_erases (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    ErasesStatePrefix (configTailFinish a peer pid ret) (peerTailFinishSource a peer pid ret) := by
  unfold configTailFinish peerTailFinishSource
  repeat' first
    | (maintenance_head configOut; exact configOut_erases _ _ _)
    | nonce_config_erasure
  all_goals try simp_all only []
  all_goals try subst_vars
  all_goals repeat' nonce_config_erasure

theorem configTail_erases (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    ErasesStatePrefix (configTail a peer pid) (peerConfigTailSource a peer pid) := by
  rw [peerConfigTailSource_factor]
  unfold configTail peerAllowedIpsSource peerAllowedIpsWith
  simp (config := {zeta := false}) only [monadLift_self]
  repeat' first
    | (maintenance_head configOut; exact configOut_erases _ _ _)
    | (maintenance_head configTailFinish; exact configTailFinish_erases _ _ _ _)
    | nonce_config_erasure
  all_goals try simp_all only []
  all_goals try subst_vars
  all_goals repeat' nonce_config_erasure

theorem configUpdate_erases (a : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    ErasesStatePrefix (configUpdate a peer flags psk pid) (peerConfigUpdateSource a peer flags psk pid) := by
  rw [peerConfigUpdateSource_factor]
  unfold configUpdate peerConfigUpdateWith
  simp (config := {zeta := false}) only [bind_assoc]
  repeat' first
    | (maintenance_head configOut; exact configOut_erases _ _ _)
    | (maintenance_head configTail; exact configTail_erases _ _ _)
    | nonce_config_erasure
  all_goals try simp_all only []
  all_goals try subst_vars
  all_goals repeat' nonce_config_erasure

theorem configPeer_erases (a : PeerAttrs) : ErasesStatePrefix (configPeer a) (setPeerCmd a) := by
  rw [← setPeerCmd_source,setPeerCmdSource_factor]
  unfold configPeer setPeerCmdWith peerCommandAcquiredWith
  repeat' first
    | (maintenance_head configOut; exact configOut_erases _ _ _)
    | (maintenance_head configUpdate; exact configUpdate_erases _ _ _ _ _)
    | nonce_config_erasure
  all_goals try simp_all only []
  all_goals try subst_vars
  all_goals repeat' nonce_config_erasure

theorem configPeers_erases (a : DeviceAttrs) : ErasesStatePrefix (configPeers a) (devicePeersSource a) := by
  unfold configPeers devicePeersWith devicePeersSource
  repeat' first
    | (maintenance_head configPeer; exact configPeer_erases _)
    | nonce_config_erasure
  all_goals try simp_all only []
  all_goals try subst_vars
  all_goals repeat' nonce_config_erasure

theorem configKey_erases (a : DeviceAttrs) : ErasesStatePrefix (configKey a) (deviceKeySource a) := by
  rw [deviceKeySource_factor]
  unfold configKey deviceKeyWith
  repeat' first
    | (maintenance_head configPeers; exact configPeers_erases _)
    | nonce_config_erasure
  all_goals try simp_all only []
  all_goals try subst_vars
  all_goals repeat' nonce_config_erasure

theorem configDeviceUpdate_erases (a : DeviceAttrs) (flags : UInt32) :
    ErasesStatePrefix (configDeviceUpdate a flags) (deviceUpdateSource a flags) := by
  unfold configDeviceUpdate deviceUpdateWith deviceUpdateSource
  repeat' first
    | (maintenance_head configKey; exact configKey_erases _)
    | nonce_config_erasure
  all_goals try simp_all only []
  all_goals try subst_vars
  all_goals repeat' nonce_config_erasure

theorem configDevice_erases (a : DeviceAttrs) : ErasesStatePrefix (configDevice a) (wgSetDevice a) := by
  rw [← wgSetDevice_source,setDeviceSource_factor]
  unfold configDevice setDeviceWith
  repeat' first
    | (maintenance_head configDeviceUpdate; exact configDeviceUpdate_erases _ _)
    | nonce_config_erasure
  all_goals try simp_all only []
  all_goals try subst_vars
  all_goals repeat' nonce_config_erasure


private theorem config_loop {α β : Type} (xs : List α) (b : β)
    (g : α → β → WGPrefix Allocation (ForInStep β))
    (hg : ∀ x b, StatePrefixPreserves (fun h w _ => Inv (view w) h) List.Nodup (g x b)) :
    StatePrefixPreserves (fun h w _ => Inv (view w) h) List.Nodup (forIn xs b g) :=
  StatePrefixEnsures.forInInvariant xs b g (fun _ h w _ => Inv (view w) h) List.Nodup
    (fun _ _ _ _ hi => hi.nodup) hg

macro "nonce_config_safe" : tactic => `(tactic| first
  | unfold StatePrefixPreserves
  | maintenance_join_let
  | maintenance_join_use
  | (nonce_source_head keepaliveObserved; exact keepaliveObserved_safe _)
  | (nonce_source_head stagingObserved; exact stagingObserved_safe _)
  | (first | nonce_source_head Pure.pure | nonce_source_head pure
     exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.nodup) (fun _ _ _ hi => hi))
  | (nonce_source_head Pure.pure; exact Frames.lift_frame (SameView.pure _ _))
  | (nonce_source_head Bind.bind; apply StatePrefixEnsures.bind)
  | (nonce_source_head ForIn.forIn; apply config_loop)
  | (first | nonce_source_head getPeer | nonce_source_head getDev | nonce_source_head setPeer
           | nonce_source_head WG.andM | nonce_source_head WG.orM | nonce_source_head branch
           | nonce_source_head peerPut | nonce_source_head setAllowedip | nonce_source_head peerRemove
           | nonce_source_head setPeerEndpoint | nonce_source_head removeByPeer | nonce_source_head peerCreate
           | nonce_source_head pubkeyLookup | nonce_source_head peerGet | nonce_source_head invariant
           | nonce_source_head generatePublic | nonce_source_head setStaticIdentityPrivateKey
           | nonce_source_head cookiePrecomputeDeviceKeys | nonce_source_head precomputeStaticStatic
           | nonce_source_head expireCurrentPeerKeypairs | nonce_source_head modifyDev
           | nonce_source_head clearPeerEndpointSrc | nonce_source_head setPort | nonce_source_head peerRemoveAll
           | nonce_source_head lookupInterface
     apply Frames.lift_preserves
     intro h
     repeat' nonce_config_native h)
  | maintenance_intro
  | maintenance_reduce
  | maintenance_reduce_match
  | (with_reducible split))

theorem configOut_safe (a : PeerAttrs) (peer : Option PeerId) (ret : Int) :
    StatePrefixPreserves (fun h w _ => Inv (view w) h) List.Nodup (configOut a peer ret) := by
  unfold configOut
  repeat' first
    | nonce_config_safe

theorem configTailFinish_safe (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    StatePrefixPreserves (fun h w _ => Inv (view w) h) List.Nodup (configTailFinish a peer pid ret) := by
  unfold configTailFinish
  repeat' first
    | (nonce_source_head configOut; exact configOut_safe _ _ _)
    | nonce_config_safe

theorem configTail_safe (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => Inv (view w) h) List.Nodup (configTail a peer pid) := by
  unfold configTail peerAllowedIpsWith
  repeat' first
    | (nonce_source_head configOut; exact configOut_safe _ _ _)
    | (nonce_source_head configTailFinish; exact configTailFinish_safe _ _ _ _)
    | nonce_config_safe

theorem configUpdate_safe (a : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => Inv (view w) h) List.Nodup (configUpdate a peer flags psk pid) := by
  unfold configUpdate peerConfigUpdateWith
  repeat' first
    | (nonce_source_head configOut; exact configOut_safe _ _ _)
    | (nonce_source_head configTail; exact configTail_safe _ _ _)
    | nonce_config_safe

theorem configPeer_safe (a : PeerAttrs) :
    StatePrefixPreserves (fun h w _ => Inv (view w) h) List.Nodup (configPeer a) := by
  unfold configPeer setPeerCmdWith peerCommandAcquiredWith
  repeat' first
    | (nonce_source_head configOut; exact configOut_safe _ _ _)
    | (nonce_source_head configUpdate; exact configUpdate_safe _ _ _ _ _)
    | nonce_config_safe

theorem configPeers_safe (a : DeviceAttrs) :
    StatePrefixPreserves (fun h w _ => Inv (view w) h) List.Nodup (configPeers a) := by
  unfold configPeers devicePeersWith
  repeat' first
    | (nonce_source_head configPeer; exact configPeer_safe _)
    | nonce_config_safe

private theorem configKeyWith_safe (a : DeviceAttrs) (next : WGPrefix Allocation Int)
    (nextSafe : StatePrefixPreserves (fun h w _ => Inv (view w) h) List.Nodup next) :
    StatePrefixPreserves (fun h w _ => Inv (view w) h) List.Nodup
      (deviceKeyWith (fun {_} a => liftWGPrefix a) (fun key => liftWGPrefix (pubkeyLookup key))
        (fun peer => liftWGPrefix (peerPut peer)) (fun peer => liftWGPrefix (peerRemove peer))
        (fun pid => liftWGPrefix (precomputeStaticStatic pid)) (fun pid => liftWGPrefix (expireCurrentPeerKeypairs pid))
        stagingObserved next a) := by
  unfold deviceKeyWith
  repeat' first
    | assumption
    | nonce_config_safe

theorem configKey_safe (a : DeviceAttrs) :
    StatePrefixPreserves (fun h w _ => Inv (view w) h) List.Nodup (configKey a) :=
  configKeyWith_safe a (configPeers a) (configPeers_safe a)

theorem configDeviceUpdate_safe (a : DeviceAttrs) (flags : UInt32) :
    StatePrefixPreserves (fun h w _ => Inv (view w) h) List.Nodup (configDeviceUpdate a flags) := by
  unfold configDeviceUpdate deviceUpdateWith
  repeat' first
    | (nonce_source_head configKey; exact configKey_safe _)
    | nonce_config_safe

theorem configDevice_safe (a : DeviceAttrs) :
    StatePrefixPreserves (fun h w _ => Inv (view w) h) List.Nodup (configDevice a) := by
  unfold configDevice setDeviceWith
  repeat' first
    | (nonce_source_head configDeviceUpdate; exact configDeviceUpdate_safe _ _)
    | nonce_config_safe

end Leanux.Proofs.WG.TransmitSecurity.Nonce
