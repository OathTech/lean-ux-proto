import Leanux.Proofs.WG.Noise.DriverTagPeerConfigurationFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags.Configuration
open Leanux Leanux.WG Lifetimes Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Leanux.Proofs.WG.Configuration

def out (attrs : PeerAttrs) (peer : Option PeerId) (ret : Int) : Obs Int :=
  liftWGPrefix (do WG.peerPut peer; _ ← branch .peerZeroPsk attrs.presharedKey.isSome; pure ret)

def tail (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) : Obs Int :=
  liftWGPrefix (peerConfigTailSource attrs peer pid)

def update (remove : Option PeerId → Obs Unit) (attrs : PeerAttrs) (peer : Option PeerId)
    (flags : UInt32) (psk : Option Key) (pid : PeerId) : Obs Int :=
  peerConfigUpdateWith (fun {_} a => liftWGPrefix a) (remove peer)
    (liftWGPrefix (do let p ← getPeer pid; setPeer pid {p with presharedKey := psk.getD []}))
    (liftWGPrefix (removeByPeer pid)) (fun e => liftWGPrefix (setPeerEndpoint pid e))
    (out attrs peer) (tail attrs peer pid) attrs flags psk

def acquired (remove : Option PeerId → Obs Unit) (attrs : PeerAttrs)
    (key : Key) (psk : Option Key) (flags : UInt32) (peer : Option PeerId) : Obs Int :=
  peerCommandAcquiredWith (fun {_} a => liftWGPrefix a) peerCreateObserved
    (fun pid => liftWGPrefix (peerGet pid)) (out attrs none) (update remove attrs) key psk flags peer

def command (remove : Option PeerId → Obs Unit) (attrs : PeerAttrs) : Obs Int :=
  setPeerCmdWith (fun {_} a => liftWGPrefix a) (fun key => liftWGPrefix (pubkeyLookup key))
    (out attrs none) (acquired remove attrs) attrs

theorem update_erases (remove : Option PeerId → Obs Unit)
    (hr : ∀ peer, ErasesStatePrefix (remove peer) (peerRemove peer))
    (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    ErasesStatePrefix (update remove attrs peer flags psk pid)
      (peerConfigUpdateSource attrs peer flags psk pid) := by
  rw [peerConfigUpdateSource_factor]
  unfold update peerConfigUpdateWith
  dsimp (config := {zeta := false}) only []
  repeat' first
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head out; exact erasesStatePrefix_lift _)
    | (maintenance_head tail; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | (maintenance_head Bind.bind; apply erasesStatePrefix_bind)
    | maintenance_intro
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_match
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | exact hr _
    | contradiction

theorem acquired_erases (remove : Option PeerId → Obs Unit)
    (hr : ∀ peer, ErasesStatePrefix (remove peer) (peerRemove peer))
    (attrs : PeerAttrs) (key : Key) (psk : Option Key) (flags : UInt32) (peer : Option PeerId) :
    ErasesStatePrefix (acquired remove attrs key psk flags peer)
      (peerCommandAcquiredWith (fun {_} a => a) peerCreate peerGet
        (fun ret => do peerPut none; _ ← branch .peerZeroPsk attrs.presharedKey.isSome; pure ret)
        (peerConfigUpdateSource attrs) key psk flags peer) := by
  unfold acquired peerCommandAcquiredWith
  dsimp (config := {zeta := false}) only []
  repeat' first
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head out; exact erasesStatePrefix_lift _)
    | (maintenance_head peerCreateObserved; exact peerCreateObserved_erases _ _)
    | (maintenance_head update; exact update_erases remove hr _ _ _ _ _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | (maintenance_head Bind.bind; apply erasesStatePrefix_bind)
    | maintenance_intro
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_match
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | contradiction

theorem command_erases (remove : Option PeerId → Obs Unit)
    (hr : ∀ peer, ErasesStatePrefix (remove peer) (peerRemove peer)) (attrs : PeerAttrs) :
    ErasesStatePrefix (command remove attrs) (setPeerCmd attrs) := by
  rw [← setPeerCmd_source,setPeerCmdSource_factor]
  unfold command setPeerCmdWith
  dsimp (config := {zeta := false}) only []
  repeat' first
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head out; exact erasesStatePrefix_lift _)
    | (maintenance_head acquired; exact acquired_erases remove hr _ _ _ _ _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | (maintenance_head Bind.bind; apply erasesStatePrefix_bind)
    | maintenance_intro
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_match
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | contradiction


theorem out_preserves (entry : TagMap) (attrs : PeerAttrs) (peer : Option PeerId) (ret : Int) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory (out attrs peer ret) := by
  apply lift_retained
  intro g ambient result final after run
  have kept : Preserves (fun w => TagsRetained (tagView g) (tagView w))
      (do WG.peerPut peer; _ ← branch .peerZeroPsk attrs.presharedKey.isSome; pure ret) :=
    preserves_bind (put_preserves peer (tagView g)) (fun _ =>
      preserves_bind (hoare_liftAmbient (AmbientM.branch _ _) _) (fun _ => preserves_pure _))
  exact (hoare_iff_run_ambient _ _ _).mp kept g ambient result final after (TagsRetained.refl _) run

theorem tail_preserves (entry : TagMap) (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory (tail attrs peer pid) :=
  lift_retained entry _ (peerTail_retained attrs peer pid)

macro "config_tag_frame" : tactic => `(tactic|
  (intro initial
   change Preserves (fun w => tagView w = initial) _
   simp (config := {zeta := false}) only [WG.andM,WG.orM,branch]
   repeat' first
     | (rx_retention_head getDev; exact (store_frame getDev_sameWGStore).wp (fun s => s = initial))
     | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
     | rx_retention_step))

macro "config_tag_step " entry:term : tactic => `(tactic| first
  | (maintenance_head out; exact out_preserves $entry _ _ _)
  | (maintenance_head tail; exact tail_preserves $entry _ _ _)
  | (maintenance_lift_action_head branch; exact ambient_preserves $entry (AmbientM.branch _ _))
  | (maintenance_lift_action_head invariant; exact ambient_preserves $entry (AmbientM.invariant _))
  | (maintenance_lift_action_head getDev; exact Flush.dev_preserves $entry)
  | (maintenance_lift_action_head WG.andM; apply lift_frame $entry; config_tag_frame)
  | (maintenance_lift_action_head WG.orM; apply lift_frame $entry; config_tag_frame)
  | (maintenance_head Pure.pure; exact pure_preserves $entry _)
  | (maintenance_head Bind.bind
     apply StatePrefixEnsures.bind (Q := fun _ h g _ => NativeInv $entry h g))
  | (maintenance_head ForIn.forIn
     apply Flush.list_preserves (fun h g _ => NativeInv $entry h g) ValidHistory
       (fun _ _ _ hi => hi.2)
     intro turn state
     unfold StatePrefixPreserves)
  | maintenance_intro
  | maintenance_join_let
  | maintenance_join_use
  | maintenance_reduce
  | maintenance_reduce_match
  | maintenance_match
  | (maintenance_head ite; split)
  | (maintenance_head dite; split)
  | contradiction)

theorem update_preserves (entry : TagMap) (remove : Option PeerId → Obs Unit)
    (hr : ∀ peer, StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory (remove peer))
    (endpoint : ∀ pid e, SameView tagView (setPeerEndpoint pid e))
    (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory
      (update remove attrs peer flags psk pid) := by
  unfold update peerConfigUpdateWith StatePrefixPreserves
  dsimp (config := {zeta := false}) only []
  repeat' first
    | (maintenance_lift_action_head setPeerEndpoint; exact lift_frame entry _ (endpoint _ _))
    | (maintenance_lift_action_head removeByPeer; exact lift_frame entry _ (removeByPeer_frame _))
    | (maintenance_lift_action_head Bind.bind
       exact lift_frame entry _ (modifyPeer_frame pid _ (fun _ => rfl)))
    | config_tag_step entry
    | exact hr _

theorem acquired_preserves (entry : TagMap) (remove : Option PeerId → Obs Unit)
    (hr : ∀ peer, StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory (remove peer))
    (endpoint : ∀ pid e, SameView tagView (setPeerEndpoint pid e))
    (attrs : PeerAttrs) (key : Key) (psk : Option Key) (flags : UInt32) (peer : Option PeerId) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory
      (acquired remove attrs key psk flags peer) := by
  unfold acquired peerCommandAcquiredWith StatePrefixPreserves
  dsimp (config := {zeta := false}) only []
  repeat' first
    | (maintenance_head peerCreateObserved; exact peerCreateObserved_preserves entry _ _)
    | (maintenance_lift_action_head peerGet; exact lift_frame entry _ (peerGet_frame _))
    | (maintenance_head update; exact update_preserves entry remove hr endpoint _ _ _ _ _)
    | config_tag_step entry

theorem command_preserves (entry : TagMap) (remove : Option PeerId → Obs Unit)
    (hr : ∀ peer, StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory (remove peer))
    (endpoint : ∀ pid e, SameView tagView (setPeerEndpoint pid e)) (attrs : PeerAttrs) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory (command remove attrs) := by
  unfold command setPeerCmdWith StatePrefixPreserves
  dsimp (config := {zeta := false}) only []
  repeat' first
    | (maintenance_lift_action_head pubkeyLookup; exact lift_frame entry _ (pubkeyLookup_frame _))
    | (maintenance_head acquired; exact acquired_preserves entry remove hr endpoint _ _ _ _ _)
    | config_tag_step entry


def devicePeers (remove : Option PeerId → Obs Unit) (attrs : DeviceAttrs) : Obs Int :=
  devicePeersWith (fun {_} a => liftWGPrefix a) (command remove) attrs

def deviceKey (remove : Option PeerId → Obs Unit) (attrs : DeviceAttrs) : Obs Int :=
  deviceKeyWith (fun {_} a => liftWGPrefix a)
    (fun key => liftWGPrefix (pubkeyLookup key)) (fun p => liftWGPrefix (WG.peerPut p)) remove
    (fun pid => liftWGPrefix (precomputeStaticStatic pid))
    (fun pid => recordHelper (.expireCurrentPeerKeypairs pid) (fun _ => .cleared) (expireCurrentPeerKeypairs pid))
    (fun pid => liftWGPrefix (sendStagedPackets pid)) (devicePeers remove attrs) attrs

def deviceUpdate (remove : Option PeerId → Obs Unit) (removeAll : Obs Unit)
    (attrs : DeviceAttrs) (flags : UInt32) : Obs Int :=
  deviceUpdateWith (fun {_} a => liftWGPrefix a) (fun pid => liftWGPrefix (clearPeerEndpointSrc pid))
    (fun port => liftWGPrefix (setPort port)) removeAll (deviceKey remove attrs) attrs flags

def device (remove : Option PeerId → Obs Unit) (removeAll : Obs Unit) (attrs : DeviceAttrs) : Obs Int :=
  setDeviceWith (fun {_} a => liftWGPrefix a) (deviceUpdate remove removeAll attrs) attrs

macro "config_tag_erasure" : tactic => `(tactic| first
  | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
  | (maintenance_head recordHelper; exact recordHelper_erases _ _ _)
  | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
  | (maintenance_head Bind.bind; apply erasesStatePrefix_bind)
  | (maintenance_head ForIn.forIn; apply erasesStatePrefix_forIn)
  | maintenance_intro
  | maintenance_erases_join
  | maintenance_erases_join_use
  | maintenance_reduce
  | maintenance_reduce_match
  | maintenance_match
  | (maintenance_head ite; split)
  | (maintenance_head dite; split)
  | contradiction)

theorem devicePeers_erases (remove : Option PeerId → Obs Unit)
    (hr : ∀ peer, ErasesStatePrefix (remove peer) (peerRemove peer)) (attrs : DeviceAttrs) :
    ErasesStatePrefix (devicePeers remove attrs) (devicePeersSource attrs) := by
  rw [devicePeersSource_factor]
  unfold devicePeers devicePeersWith
  dsimp (config := {zeta := false}) only []
  repeat' first
    | (maintenance_head command; exact command_erases remove hr _)
    | config_tag_erasure

theorem deviceKey_erases (remove : Option PeerId → Obs Unit)
    (hr : ∀ peer, ErasesStatePrefix (remove peer) (peerRemove peer)) (attrs : DeviceAttrs) :
    ErasesStatePrefix (deviceKey remove attrs) (deviceKeySource attrs) := by
  rw [deviceKeySource_factor]
  unfold deviceKey deviceKeyWith
  dsimp (config := {zeta := false}) only []
  repeat' first
    | (maintenance_head devicePeers; exact devicePeers_erases remove hr _)
    | config_tag_erasure
    | exact hr _

theorem deviceUpdate_erases (remove : Option PeerId → Obs Unit) (removeAll : Obs Unit)
    (hr : ∀ peer, ErasesStatePrefix (remove peer) (peerRemove peer))
    (ha : ErasesStatePrefix removeAll peerRemoveAll) (attrs : DeviceAttrs) (flags : UInt32) :
    ErasesStatePrefix (deviceUpdate remove removeAll attrs flags) (deviceUpdateSource attrs flags) := by
  rw [deviceUpdateSource_factor]
  unfold deviceUpdate deviceUpdateWith
  dsimp (config := {zeta := false}) only []
  repeat' first
    | (maintenance_head deviceKey; exact deviceKey_erases remove hr _)
    | config_tag_erasure
    | exact ha

theorem device_erases (remove : Option PeerId → Obs Unit) (removeAll : Obs Unit)
    (hr : ∀ peer, ErasesStatePrefix (remove peer) (peerRemove peer))
    (ha : ErasesStatePrefix removeAll peerRemoveAll) (attrs : DeviceAttrs) :
    ErasesStatePrefix (device remove removeAll attrs) (wgSetDevice attrs) := by
  rw [← wgSetDevice_source,setDeviceSource_factor]
  unfold device setDeviceWith
  dsimp (config := {zeta := false}) only []
  repeat' first
    | (maintenance_head deviceUpdate; exact deviceUpdate_erases remove removeAll hr ha _ _)
    | config_tag_erasure

theorem devicePeers_preserves (entry : TagMap) (remove : Option PeerId → Obs Unit)
    (hr : ∀ peer, StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory (remove peer))
    (endpoint : ∀ pid e, SameView tagView (setPeerEndpoint pid e)) (attrs : DeviceAttrs) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory (devicePeers remove attrs) := by
  unfold devicePeers devicePeersWith StatePrefixPreserves
  dsimp (config := {zeta := false}) only []
  repeat' first
    | (maintenance_head command; exact command_preserves entry remove hr endpoint _)
    | config_tag_step entry

theorem deviceKey_preserves (entry : TagMap) (remove : Option PeerId → Obs Unit)
    (hr : ∀ peer, StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory (remove peer))
    (endpoint : ∀ pid e, SameView tagView (setPeerEndpoint pid e)) (attrs : DeviceAttrs) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory (deviceKey remove attrs) := by
  unfold deviceKey deviceKeyWith StatePrefixPreserves
  dsimp (config := {zeta := false}) only []
  repeat' first
    | (maintenance_head devicePeers; exact devicePeers_preserves entry remove hr endpoint _)
    | (maintenance_head recordHelper; exact recordHelper_preserves entry _ _ _ rfl)
    | (maintenance_lift_action_head generatePublic
       exact lift_frame entry _ ((generatePublic_sameWGWorld _).factor tagView))
    | (maintenance_lift_action_head pubkeyLookup
       exact lift_frame entry _ (pubkeyLookup_frame _))
    | (maintenance_lift_action_head peerPut
       exact lift_retained entry _ (Index.staging_tags _ (fun initial => Index.staging_peerPut initial _)))
    | (maintenance_lift_action_head precomputeStaticStatic
       exact lift_frame entry _ (precomputeStaticStatic_frame _))
    | (maintenance_lift_action_head sendStagedPackets
       exact lift_retained entry _ (Index.sendStagedPackets_tags_retained _))
    | (maintenance_lift_action_head setStaticIdentityPrivateKey
       exact lift_frame entry _ (configuration_frame (setStaticIdentityPrivateKey_sameConfiguration _)))
    | (maintenance_lift_action_head cookiePrecomputeDeviceKeys
       exact lift_frame entry _ (configuration_frame cookiePrecomputeDeviceKeys_sameConfiguration))
    | config_tag_step entry
    | exact hr _

theorem deviceUpdate_preserves (entry : TagMap) (remove : Option PeerId → Obs Unit) (removeAll : Obs Unit)
    (hr : ∀ peer, StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory (remove peer))
    (ha : StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory removeAll)
    (endpoint : ∀ pid e, SameView tagView (setPeerEndpoint pid e))
    (clear : ∀ pid, SameView tagView (clearPeerEndpointSrc pid))
    (port : ∀ n, SameView tagView (setPort n))
    (attrs : DeviceAttrs) (flags : UInt32) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory
      (deviceUpdate remove removeAll attrs flags) := by
  unfold deviceUpdate deviceUpdateWith StatePrefixPreserves
  dsimp (config := {zeta := false}) only []
  repeat' first
    | (maintenance_head deviceKey; exact deviceKey_preserves entry remove hr endpoint _)
    | (maintenance_lift_action_head clearPeerEndpointSrc; exact lift_frame entry _ (clear _))
    | (maintenance_lift_action_head setPort; exact lift_frame entry _ (port _))
    | (maintenance_lift_action_head modifyDev
       exact lift_frame entry _ (modifyDev_frame _ (fun _ => rfl)))
    | config_tag_step entry
    | exact ha

theorem device_preserves (entry : TagMap) (remove : Option PeerId → Obs Unit) (removeAll : Obs Unit)
    (hr : ∀ peer, StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory (remove peer))
    (ha : StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory removeAll)
    (endpoint : ∀ pid e, SameView tagView (setPeerEndpoint pid e))
    (clear : ∀ pid, SameView tagView (clearPeerEndpointSrc pid))
    (port : ∀ n, SameView tagView (setPort n)) (attrs : DeviceAttrs) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory (device remove removeAll attrs) := by
  unfold device setDeviceWith StatePrefixPreserves
  dsimp (config := {zeta := false}) only []
  repeat' first
    | (maintenance_head deviceUpdate
       exact deviceUpdate_preserves entry remove removeAll hr ha endpoint clear port _ _)
    | (maintenance_lift_action_head lookupInterface
       exact lift_frame entry _ ((lookupInterface_sameWGWorld _).factor tagView))
    | config_tag_step entry


/-- Actual peer configuration: births and helper edges are journalled;
removal executes its actual receipt-bearing drains. -/
def observePeer (attrs : PeerAttrs) : Obs Int :=
  command Removal.removeObserved attrs

/-- Actual device configuration, including private-key expiry and both
peer-removal paths. No success, residency, or attribute-shape premise. -/
def observeDevice (attrs : DeviceAttrs) : Obs Int :=
  device Removal.removeObserved Removal.removeAllObserved attrs

theorem observePeer_erases (attrs : PeerAttrs) :
    ErasesStatePrefix (observePeer attrs) (setPeerCmd attrs) :=
  command_erases Removal.removeObserved Removal.removeObserved_erases attrs

theorem observeDevice_erases (attrs : DeviceAttrs) :
    ErasesStatePrefix (observeDevice attrs) (wgSetDevice attrs) :=
  device_erases Removal.removeObserved Removal.removeAllObserved
    Removal.removeObserved_erases Removal.removeAllObserved_erases attrs

theorem observePeer_preserves (entry : TagMap) (attrs : PeerAttrs) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory (observePeer attrs) :=
  command_preserves entry Removal.removeObserved (Removal.removeObserved_preserves entry)
    setPeerEndpoint_frame attrs

theorem observeDevice_preserves (entry : TagMap) (attrs : DeviceAttrs) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory (observeDevice attrs) :=
  device_preserves entry Removal.removeObserved Removal.removeAllObserved
    (Removal.removeObserved_preserves entry) (Removal.removeAllObserved_preserves entry)
    setPeerEndpoint_frame clearPeerEndpointSrc_frame setPort_frame attrs

end Leanux.Proofs.WG.Noise.DriverTags.Configuration
