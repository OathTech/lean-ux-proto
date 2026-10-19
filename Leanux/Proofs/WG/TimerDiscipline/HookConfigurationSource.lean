import Leanux.Proofs.WG.Queues.JointDevice
import Leanux.Proofs.WG.Noise.DriverTagFlushSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookConfiguration
open Leanux Leanux.WG Lifetimes Leanux.Proofs.Logged
open Leanux.Proofs.WG.Configuration
variable {E α : Type}

def out (attrs : PeerAttrs) (peer : Option PeerId) (ret : Int) : WGPrefix E Int :=
  liftWGPrefix (do WG.peerPut peer; _ ← branch .peerZeroPsk attrs.presharedKey.isSome; pure ret)

def tail (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) : WGPrefix E Int :=
  liftWGPrefix (peerConfigTailSource attrs peer pid)

def update (remove : Option PeerId → WGPrefix E Unit) (attrs : PeerAttrs)
    (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) : WGPrefix E Int :=
  peerConfigUpdateWith (fun {_} a=>liftWGPrefix a) (remove peer)
    (liftWGPrefix (do let p ←getPeer pid; setPeer pid {p with presharedKey:=psk.getD []}))
    (liftWGPrefix (removeByPeer pid)) (fun e=>liftWGPrefix (setPeerEndpoint pid e))
    (out attrs peer) (tail attrs peer pid) attrs flags psk

def acquired (remove : Option PeerId → WGPrefix E Unit) (attrs : PeerAttrs)
    (key : Key) (psk : Option Key) (flags : UInt32) (peer : Option PeerId) : WGPrefix E Int :=
  peerCommandAcquiredWith (fun {_} a=>liftWGPrefix a)
    (fun k p=>liftWGPrefix (peerCreate k p)) (fun pid=>liftWGPrefix (peerGet pid))
    (out attrs none) (update remove attrs) key psk flags peer

def command (remove : Option PeerId → WGPrefix E Unit) (attrs : PeerAttrs) : WGPrefix E Int :=
  setPeerCmdWith (fun {_} a=>liftWGPrefix a) (fun key=>liftWGPrefix (pubkeyLookup key))
    (out attrs none) (acquired remove attrs) attrs

def devicePeers (remove : Option PeerId → WGPrefix E Unit) (attrs : DeviceAttrs) : WGPrefix E Int :=
  devicePeersWith (fun {_} a=>liftWGPrefix a) (command remove) attrs

def deviceKey (remove : Option PeerId → WGPrefix E Unit) (attrs : DeviceAttrs) : WGPrefix E Int :=
  deviceKeyWith (fun {_} a=>liftWGPrefix a)
    (fun key=>liftWGPrefix (pubkeyLookup key)) (fun p=>liftWGPrefix (WG.peerPut p)) remove
    (fun pid=>liftWGPrefix (precomputeStaticStatic pid))
    (fun pid=>liftWGPrefix (expireCurrentPeerKeypairs pid))
    (fun pid=>liftWGPrefix (sendStagedPackets pid)) (devicePeers remove attrs) attrs

def deviceUpdate (remove : Option PeerId → WGPrefix E Unit) (removeAll : WGPrefix E Unit)
    (attrs : DeviceAttrs) (flags : UInt32) : WGPrefix E Int :=
  deviceUpdateWith (fun {_} a=>liftWGPrefix a) (fun pid=>liftWGPrefix (clearPeerEndpointSrc pid))
    (fun port=>liftWGPrefix (setPort port)) removeAll (deviceKey remove attrs) attrs flags

def device (remove : Option PeerId → WGPrefix E Unit) (removeAll : WGPrefix E Unit)
    (attrs : DeviceAttrs) : WGPrefix E Int :=
  setDeviceWith (fun {_} a=>liftWGPrefix a) (deviceUpdate remove removeAll attrs) attrs

macro "hook_configuration_erase" : tactic => `(tactic| first
  | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
  | (maintenance_head out; exact erasesStatePrefix_lift _)
  | (maintenance_head tail; exact erasesStatePrefix_lift _)
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

theorem update_erases (remove : Option PeerId → WGPrefix E Unit)
    (hr : ∀ peer, ErasesStatePrefix (remove peer) (peerRemove peer))
    (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    ErasesStatePrefix (update remove attrs peer flags psk pid)
      (peerConfigUpdateSource attrs peer flags psk pid) := by
  rw [peerConfigUpdateSource_factor]
  unfold update peerConfigUpdateWith
  dsimp (config := {zeta := false}) only []
  repeat' first | exact hr _ | hook_configuration_erase

theorem acquired_erases (remove : Option PeerId → WGPrefix E Unit)
    (hr : ∀ peer, ErasesStatePrefix (remove peer) (peerRemove peer))
    (attrs : PeerAttrs) (key : Key) (psk : Option Key) (flags : UInt32) (peer : Option PeerId) :
    ErasesStatePrefix (acquired remove attrs key psk flags peer)
      (peerCommandAcquiredWith (fun {_} a=>a) peerCreate peerGet
        (fun ret=>do peerPut none; _ ←branch .peerZeroPsk attrs.presharedKey.isSome; pure ret)
        (peerConfigUpdateSource attrs) key psk flags peer) := by
  unfold acquired peerCommandAcquiredWith
  dsimp (config := {zeta := false}) only []
  repeat' first
    | (maintenance_head update; exact update_erases remove hr _ _ _ _ _)
    | hook_configuration_erase

theorem command_erases (remove : Option PeerId → WGPrefix E Unit)
    (hr : ∀ peer, ErasesStatePrefix (remove peer) (peerRemove peer)) (attrs : PeerAttrs) :
    ErasesStatePrefix (command remove attrs) (setPeerCmd attrs) := by
  rw [←setPeerCmd_source,setPeerCmdSource_factor]
  unfold command setPeerCmdWith
  dsimp (config := {zeta := false}) only []
  repeat' first
    | (maintenance_head acquired; exact acquired_erases remove hr _ _ _ _ _)
    | hook_configuration_erase

theorem devicePeers_erases (remove : Option PeerId → WGPrefix E Unit)
    (hr : ∀ peer, ErasesStatePrefix (remove peer) (peerRemove peer)) (attrs : DeviceAttrs) :
    ErasesStatePrefix (devicePeers remove attrs) (devicePeersSource attrs) := by
  rw [devicePeersSource_factor]
  unfold devicePeers devicePeersWith
  dsimp (config := {zeta := false}) only []
  repeat' first
    | (maintenance_head command; exact command_erases remove hr _)
    | hook_configuration_erase

theorem deviceKey_erases (remove : Option PeerId → WGPrefix E Unit)
    (hr : ∀ peer, ErasesStatePrefix (remove peer) (peerRemove peer)) (attrs : DeviceAttrs) :
    ErasesStatePrefix (deviceKey remove attrs) (deviceKeySource attrs) := by
  rw [deviceKeySource_factor]
  unfold deviceKey deviceKeyWith
  dsimp (config := {zeta := false}) only []
  repeat' first
    | (maintenance_head devicePeers; exact devicePeers_erases remove hr _)
    | exact hr _
    | hook_configuration_erase

theorem deviceUpdate_erases (remove : Option PeerId → WGPrefix E Unit) (removeAll : WGPrefix E Unit)
    (hr : ∀ peer, ErasesStatePrefix (remove peer) (peerRemove peer))
    (ha : ErasesStatePrefix removeAll peerRemoveAll) (attrs : DeviceAttrs) (flags : UInt32) :
    ErasesStatePrefix (deviceUpdate remove removeAll attrs flags) (deviceUpdateSource attrs flags) := by
  rw [deviceUpdateSource_factor]
  unfold deviceUpdate deviceUpdateWith
  dsimp (config := {zeta := false}) only []
  repeat' first
    | (maintenance_head deviceKey; exact deviceKey_erases remove hr _)
    | exact ha
    | hook_configuration_erase

theorem device_erases (remove : Option PeerId → WGPrefix E Unit) (removeAll : WGPrefix E Unit)
    (hr : ∀ peer, ErasesStatePrefix (remove peer) (peerRemove peer))
    (ha : ErasesStatePrefix removeAll peerRemoveAll) (attrs : DeviceAttrs) :
    ErasesStatePrefix (device remove removeAll attrs) (wgSetDevice attrs) := by
  rw [←wgSetDevice_source,setDeviceSource_factor]
  unfold device setDeviceWith
  dsimp (config := {zeta := false}) only []
  repeat' first
    | (maintenance_head deviceUpdate; exact deviceUpdate_erases remove removeAll hr ha _ _)
    | hook_configuration_erase

theorem lift_preserves (S : List E → Prop) (action : WG.M α) :
    StatePrefixPreserves (fun h _ _=>S h) S (liftWGPrefix action) :=
  StatePrefixEnsures.lift action (fun _ _ _ hi=>hi) (fun _ _ _ _ _ _ hi _=>hi)

macro "hook_configuration_keep " predicate:term : tactic => `(tactic| first
  | (maintenance_head liftWGPrefix; exact lift_preserves $predicate _)
  | (maintenance_head out; exact lift_preserves $predicate _)
  | (maintenance_head tail; exact lift_preserves $predicate _)
  | (maintenance_head Pure.pure
     exact StatePrefixEnsures.pure _ (fun _ _ _ hi=>hi) (fun _ _ _ hi=>hi))
  | (maintenance_head Bind.bind
     apply StatePrefixEnsures.bind (Q:=fun _ h _ _=>$predicate h))
  | (maintenance_head ForIn.forIn
     apply Noise.DriverTags.Flush.list_preserves (fun h _ _=>$predicate h) $predicate
       (fun _ _ _ hi=>hi)
     intro item state
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

theorem update_preserves (S : List E → Prop) (remove : Option PeerId → WGPrefix E Unit)
    (hr : ∀ peer, StatePrefixPreserves (fun h _ _=>S h) S (remove peer))
    (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    StatePrefixPreserves (fun h _ _=>S h) S (update remove attrs peer flags psk pid) := by
  unfold update peerConfigUpdateWith StatePrefixPreserves
  dsimp (config := {zeta := false}) only []
  repeat' first | exact hr _ | hook_configuration_keep S

theorem acquired_preserves (S : List E → Prop) (remove : Option PeerId → WGPrefix E Unit)
    (hr : ∀ peer, StatePrefixPreserves (fun h _ _=>S h) S (remove peer))
    (attrs : PeerAttrs) (key : Key) (psk : Option Key) (flags : UInt32) (peer : Option PeerId) :
    StatePrefixPreserves (fun h _ _=>S h) S (acquired remove attrs key psk flags peer) := by
  unfold acquired peerCommandAcquiredWith StatePrefixPreserves
  dsimp (config := {zeta := false}) only []
  repeat' first
    | (maintenance_head update; exact update_preserves S remove hr _ _ _ _ _)
    | hook_configuration_keep S

theorem command_preserves (S : List E → Prop) (remove : Option PeerId → WGPrefix E Unit)
    (hr : ∀ peer, StatePrefixPreserves (fun h _ _=>S h) S (remove peer)) (attrs : PeerAttrs) :
    StatePrefixPreserves (fun h _ _=>S h) S (command remove attrs) := by
  unfold command setPeerCmdWith StatePrefixPreserves
  dsimp (config := {zeta := false}) only []
  repeat' first
    | (maintenance_head acquired; exact acquired_preserves S remove hr _ _ _ _ _)
    | hook_configuration_keep S

theorem devicePeers_preserves (S : List E → Prop) (remove : Option PeerId → WGPrefix E Unit)
    (hr : ∀ peer, StatePrefixPreserves (fun h _ _=>S h) S (remove peer)) (attrs : DeviceAttrs) :
    StatePrefixPreserves (fun h _ _=>S h) S (devicePeers remove attrs) := by
  unfold devicePeers devicePeersWith StatePrefixPreserves
  dsimp (config := {zeta := false}) only []
  repeat' first
    | (maintenance_head command; exact command_preserves S remove hr _)
    | hook_configuration_keep S

theorem deviceKey_preserves (S : List E → Prop) (remove : Option PeerId → WGPrefix E Unit)
    (hr : ∀ peer, StatePrefixPreserves (fun h _ _=>S h) S (remove peer)) (attrs : DeviceAttrs) :
    StatePrefixPreserves (fun h _ _=>S h) S (deviceKey remove attrs) := by
  unfold deviceKey deviceKeyWith StatePrefixPreserves
  dsimp (config := {zeta := false}) only []
  repeat' first
    | (maintenance_head devicePeers; exact devicePeers_preserves S remove hr _)
    | exact hr _
    | hook_configuration_keep S

theorem deviceUpdate_preserves (S : List E → Prop) (remove : Option PeerId → WGPrefix E Unit)
    (removeAll : WGPrefix E Unit)
    (hr : ∀ peer, StatePrefixPreserves (fun h _ _=>S h) S (remove peer))
    (ha : StatePrefixPreserves (fun h _ _=>S h) S removeAll) (attrs : DeviceAttrs) (flags : UInt32) :
    StatePrefixPreserves (fun h _ _=>S h) S (deviceUpdate remove removeAll attrs flags) := by
  unfold deviceUpdate deviceUpdateWith StatePrefixPreserves
  dsimp (config := {zeta := false}) only []
  repeat' first
    | (maintenance_head deviceKey; exact deviceKey_preserves S remove hr _)
    | exact ha
    | hook_configuration_keep S

theorem device_preserves (S : List E → Prop) (remove : Option PeerId → WGPrefix E Unit)
    (removeAll : WGPrefix E Unit)
    (hr : ∀ peer, StatePrefixPreserves (fun h _ _=>S h) S (remove peer))
    (ha : StatePrefixPreserves (fun h _ _=>S h) S removeAll) (attrs : DeviceAttrs) :
    StatePrefixPreserves (fun h _ _=>S h) S (device remove removeAll attrs) := by
  unfold device setDeviceWith StatePrefixPreserves
  dsimp (config := {zeta := false}) only []
  repeat' first
    | (maintenance_head deviceUpdate; exact deviceUpdate_preserves S remove removeAll hr ha _ _)
    | hook_configuration_keep S

theorem appends_true (action : WGPrefix E α) (ha : StateAppends action) :
    StatePrefixPreserves (fun _ _ _=>True) (fun _=>True) action := by
  intro g a h _
  obtain ⟨suffix, same⟩ := ha g a h
  refine ⟨suffix,same,True.intro,?_⟩
  cases (runPrefix (action.run g) a h).1 <;> trivial

theorem command_appends (remove : Option PeerId → WGPrefix E Unit)
    (hr : ∀ peer, StateAppends (remove peer)) (attrs : PeerAttrs) :
    StateAppends (command remove attrs) := by
  intro g a h
  obtain ⟨suffix,same,_,_⟩ := command_preserves (fun _=>True) remove
    (fun p=>appends_true _ (hr p)) attrs g a h True.intro
  exact ⟨suffix,same⟩

theorem device_appends (remove : Option PeerId → WGPrefix E Unit) (removeAll : WGPrefix E Unit)
    (hr : ∀ peer, StateAppends (remove peer)) (ha : StateAppends removeAll) (attrs : DeviceAttrs) :
    StateAppends (device remove removeAll attrs) := by
  intro g a h
  obtain ⟨suffix,same,_,_⟩ := device_preserves (fun _=>True) remove removeAll
    (fun p=>appends_true _ (hr p)) (appends_true _ ha) attrs g a h True.intro
  exact ⟨suffix,same⟩

end Leanux.Proofs.WG.TimerDiscipline.HookConfiguration
