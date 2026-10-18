import Leanux.Proofs.WG.Origins.RetainingLifecycle
import Leanux.Proofs.Framing.WGAllowedIpsInsert
import Leanux.Proofs.WG.Configuration.AllowedIpSource
import Leanux.Proofs.WG.Configuration.DeviceSource

/-! Original configuration preserves receiving material on every normal return,
including negative errno after partial updates. Erasure and invalidation are
permitted. This is not peer-identity preservation or a returned-state claim on Stop. -/
namespace Leanux.Proofs.WG.Origins.Retaining
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Leanux.Proofs.WG.Configuration Leanux.Proofs.WG.Queues Leanux.Proofs.WG.Lifetimes Std.Do
set_option pp.structureInstances false

/-- The original conditional mask transport admits arbitrary actual stacks,
including product actions; no other component's state is added to its premise. -/
theorem nodeAllocation_material {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun s => nodeAllocationView (project s)) a) :
    SameView (fun s => view (project s)) a := by
  apply ha.of_factor (fun k : WGStoreView => k.dev.map materialState) _
  intro w
  simp [view,nodeAllocationView,nodeAllocationDevice,nodeDevice,wgStoreView,
    materialState,Option.map_map,Function.comp_def]

macro "configuration_basic " P:term : tactic => `(tactic| first
  | (index_material_head IndexOwner.setPeerWord; unfold IndexOwner.setPeerWord)
  | (index_material_head liftM; unfold liftM)
  | (index_material_head commonBits; unfold commonBits; try material_lower)
  | (index_material_head choose; unfold choose; try material_lower)
  | (index_material_head AipNode.bitAt; unfold AipNode.bitAt; try material_lower)
  | lifecycle_basic $P)

macro "configuration_entry " initial:ident : tactic => `(tactic| (
  intro $initial:ident
  refine hoare_consequence (m := AmbientM)
    (P := fun w : WGWorld => RetainsView $initial (view w))
    (Q := fun _ (w : WGWorld) => RetainsView $initial (view w)) ?_
    (fun w h => by change view w = $initial at h; rw [h]; exact RetainsView.refl _)
    (fun _ _ h => h)))

theorem listAddTail_material (pid : PeerId) (id : NodeId) :
    SameView view (listAddTail pid id) := by
  intro initial
  unfold listAddTail
  try material_lower
  repeat' configuration_basic (fun t => t = initial)

theorem add_material (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    SameView view (add root bits key cidr peer) := by
  intro initial
  unfold add
  try material_lower
  repeat' first
    | (index_material_head listAddTail; exact (listAddTail_material _ _).wp (fun t => t = initial))
    | (index_material_head listDel; exact (listDel_material _).wp (fun t => t = initial))
    | configuration_basic (fun t => t = initial)

theorem insert_material (family addr cidr : Nat) (pid : PeerId) :
    SameView view (insert family addr cidr pid) := by
  intro initial
  unfold WG.insert
  try material_lower
  repeat' first
    | (index_material_head add; exact (add_material _ _ _ _ _).wp (fun t => t = initial))
    | configuration_basic (fun t => t = initial)

theorem setAllowedip_material (pid : PeerId) (ip : AllowedIpAttrs) :
    SameView view (setAllowedip pid ip) := by
  intro initial
  unfold setAllowedip
  try material_lower
  repeat' first
    | (index_material_head WG.insert; exact (insert_material _ _ _ _).wp (fun t => t = initial))
    | configuration_basic (fun t => t = initial)

theorem precomputeStaticStatic_material (pid : PeerId) :
    SameView view (precomputeStaticStatic pid) := by
  intro initial
  unfold precomputeStaticStatic
  try material_lower
  repeat' configuration_basic (fun t => t = initial)

theorem handshakeInit_material (pid : PeerId) (psk : Option Key) :
    SameView view (handshakeInit pid psk) := by
  intro initial
  unfold handshakeInit
  try material_lower
  repeat' first
    | (index_material_head precomputeStaticStatic
       exact (precomputeStaticStatic_material _).wp (fun t => t = initial))
    | configuration_basic (fun t => t = initial)

theorem peerCreate_material (key : Key) (psk : Option Key) :
    SameView view (peerCreate key psk) := by
  intro initial
  unfold peerCreate
  try material_lower
  repeat' first
    | (index_material_head handshakeInit; exact (handshakeInit_material _ _).wp (fun t => t = initial))
    | (index_material_head dstCacheReset; exact (dstCacheReset_material _).wp (fun t => t = initial))
    | (index_material_head resetLastSentHandshake
       exact (resetLastSentHandshake_material _).wp (fun t => t = initial))
    | configuration_basic (fun t => t = initial)

theorem peerTailFinish_material (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    RetainsCall (peerTailFinishSource a peer pid ret) := by
  configuration_entry initial
  unfold peerTailFinishSource
  try material_lower
  repeat' first
    | (index_material_head sendKeepalive; exact (sendKeepalive_material _).wp initial)
    | (index_material_head sendStagedPackets; exact (sendStagedPackets_material _).wp initial)
    | configuration_basic (RetainsView initial)

theorem peerConfigTail_material (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    RetainsCall (peerConfigTailSource a peer pid) := by
  rw [peerConfigTailSource_factor]
  configuration_entry initial
  unfold peerAllowedIpsSource peerAllowedIpsWith
  simp (config := {zeta := false}) only [monadLift_self]
  try material_lower
  repeat' first
    | (index_material_head setAllowedip; exact (setAllowedip_material _ _).wp (RetainsView initial))
    | (index_material_head peerTailFinishSource; exact (peerTailFinish_material _ _ _ _).wp initial)
    | configuration_basic (RetainsView initial)

theorem peerConfigUpdate_material (a : PeerAttrs) (peer : Option PeerId)
    (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    RetainsCall (peerConfigUpdateSource a peer flags psk pid) := by
  configuration_entry initial
  unfold peerConfigUpdateSource
  try material_lower
  repeat' first
    | (index_material_head peerRemove; exact (peerRemove_material _).wp initial)
    | (index_material_head setPeerEndpoint; exact (setPeerEndpoint_material _ _).wp (RetainsView initial))
    | (index_material_head removeByPeer; exact (removeByPeer_material _).wp (RetainsView initial))
    | (index_material_head peerConfigTailSource; exact (peerConfigTail_material _ _ _).wp initial)
    | configuration_basic (RetainsView initial)

theorem setPeerCmd_material (a : PeerAttrs) : RetainsCall (setPeerCmd a) := by
  rw [← setPeerCmd_source]
  configuration_entry initial
  unfold setPeerCmdSource
  try material_lower
  repeat' first
    | (index_material_head pubkeyLookup; exact (pubkeyLookup_material _).wp (RetainsView initial))
    | (index_material_head peerCreate; exact (peerCreate_material _ _).wp (RetainsView initial))
    | (index_material_head peerConfigUpdateSource; exact (peerConfigUpdate_material _ _ _ _ _).wp initial)
    | configuration_basic (RetainsView initial)

theorem devicePeers_material (a : DeviceAttrs) : RetainsCall (devicePeersSource a) := by
  configuration_entry initial
  unfold devicePeersSource
  try material_lower
  repeat' first
    | (index_material_head setPeerCmd; exact (setPeerCmd_material _).wp initial)
    | configuration_basic (RetainsView initial)

theorem deviceKey_material (a : DeviceAttrs) : RetainsCall (deviceKeySource a) := by
  configuration_entry initial
  unfold deviceKeySource
  try material_lower
  repeat' first
    | (index_material_head pubkeyLookup; exact (pubkeyLookup_material _).wp (RetainsView initial))
    | (index_material_head peerRemove; exact (peerRemove_material _).wp initial)
    | (index_material_head setStaticIdentityPrivateKey
       exact (configuration_material (project := id) _
         ((setStaticIdentityPrivateKey_sameConfiguration _).factor WGOwnedView.toWGStoreView)).wp (RetainsView initial))
    | (index_material_head cookiePrecomputeDeviceKeys
       exact (configuration_material (project := id) _
         (cookiePrecomputeDeviceKeys_sameConfiguration.factor WGOwnedView.toWGStoreView)).wp (RetainsView initial))
    | (index_material_head precomputeStaticStatic; exact (precomputeStaticStatic_material _).wp (RetainsView initial))
    | (index_material_head expireCurrentPeerKeypairs; exact (expireCurrentPeerKeypairs_material _).wp initial)
    | (index_material_head sendStagedPackets; exact (sendStagedPackets_material _).wp initial)
    | (index_material_head devicePeersSource; exact (devicePeers_material _).wp initial)
    | configuration_basic (RetainsView initial)

theorem deviceUpdate_material (a : DeviceAttrs) (flags : UInt32) :
    RetainsCall (deviceUpdateSource a flags) := by
  configuration_entry initial
  unfold deviceUpdateSource
  try material_lower
  repeat' first
    | (index_material_head clearPeerEndpointSrc; exact (clearPeerEndpointSrc_material _).wp (RetainsView initial))
    | (index_material_head setPort; exact (setPort_material _).wp (RetainsView initial))
    | (index_material_head peerRemoveAll; exact peerRemoveAll_material.wp initial)
    | (index_material_head deviceKeySource; exact (deviceKey_material _).wp initial)
    | configuration_basic (RetainsView initial)

theorem wgSetDevice_material (a : DeviceAttrs) : RetainsCall (wgSetDevice a) := by
  rw [← wgSetDevice_source]
  configuration_entry initial
  unfold wgSetDeviceSource
  try material_lower
  repeat' first
    | (index_material_head lookupInterface
       exact ((lookupInterface_sameWGWorld _).factor view).wp (RetainsView initial))
    | (index_material_head deviceUpdateSource; exact (deviceUpdate_material _ _).wp initial)
    | configuration_basic (RetainsView initial)

end Leanux.Proofs.WG.Origins.Retaining
