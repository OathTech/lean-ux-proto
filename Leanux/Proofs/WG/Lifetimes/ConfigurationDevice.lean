import Leanux.Proofs.WG.Lifetimes.ConfigurationDeviceFrames
import Leanux.Proofs.WG.Configuration.DeviceSource

/-! Complete original device configuration, factored at its actual continuations.
Every scalar-ID loop calls observed resident helpers; ordinary errors execute
the zero-key record, whereas Stops retain the reached prefix and skip it. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Leanux.Proofs.WG.Configuration
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

def devicePeersPrefix (a : DeviceAttrs) : MixedM Int := do
  let zero (ret : Int) : MixedM Int := do
    _ ← rxBranch .setDevZeroKey a.privateKey.isSome   -- memzero_explicit
    return ret
  if ← rxBranch .setDevHasPeers a.peers.isSome then
    for entry in a.peers.getD [] do
      _ ← rxBranch .setDevPeersIter true
      match entry with
      | .malformed =>   -- nla_parse_nested: NLA_F_NESTED missing, -EINVAL
        _ ← rxBranch .setDevParseErr true
        return ← zero (-EINVAL)
      | .attrs p =>
        _ ← rxBranch .setDevParseErr false
        let ret ← setPeerCmdPrefix p
        if ← rxBranch .setDevSetPeerErr (ret < 0) then return ← zero ret
    _ ← rxBranch .setDevPeersIter false
  zero 0

def deviceKeyPrefix (a : DeviceAttrs) : MixedM Int := do
  if ← andPrefix (rxBranch .setDevHasPrivateKey a.privateKey.isSome) (rxBranch .setDevPrivateKeyLen true) then
    let some key := a.privateKey | liftPrefix (invariant "unreachable")
    -- `!crypto_memneq(static_private, private_key)`: the stored key is clamped
    if !(← rxBranch .setDevKeyUnchanged ((← liftPrefix getDev).staticIdentity.staticPrivate == key)) then
      -- remove the peer whose public key the device is about to take
      let (pub, ok) ← liftPrefix (generatePublic key)
      if ← rxBranch .setDevGenPublic ok then
        let some pub := pub | liftPrefix (invariant "a generated public key without a write")
        let peer ← pubkeyLookupPrefix pub
        if ← rxBranch .setDevOldPeer peer.isSome then
          peerPutMixed peer
          peerRemovePrefix peer
      let d ← liftPrefix getDev
      let sendStaged ← andPrefix (rxBranch .setDevSendStagedNoIdentity !d.staticIdentity.hasIdentity)
        (rxBranch .setDevSendStagedRunning d.running)
      liftPrefix (setStaticIdentityPrivateKey key)
      let hasIdentity := (← liftPrefix getDev).staticIdentity.hasIdentity
      let sendStaged ← andPrefix (rxBranch .setDevSendStagedKept sendStaged) (rxBranch .setDevSendStagedHasIdentity hasIdentity)
      liftPrefix cookiePrecomputeDeviceKeys
      for pid in (← liftPrefix getDev).peerList do
        _ ← rxBranch .setDevKeyPeerIter true
        precomputeStaticStaticMixed pid
        expireCurrentPeerKeypairsPrefix pid
        if ← rxBranch .setDevSendStagedPeer sendStaged then sendStagedPacketsPrefix pid
      _ ← rxBranch .setDevKeyPeerIter false
  devicePeersPrefix a

def deviceUpdatePrefix (a : DeviceAttrs) (flags : UInt32) : MixedM Int := do
  let zero (ret : Int) : MixedM Int := do
    _ ← rxBranch .setDevZeroKey a.privateKey.isSome   -- memzero_explicit
    return ret
  liftPrefix (modifyDev fun d => { d with deviceUpdateGen := d.deviceUpdateGen + 1 })
  if ← rxBranch .setDevFwmark a.fwmark.isSome then
    liftPrefix (modifyDev fun d => { d with fwmark := a.fwmark.getD 0 })
    for pid in (← liftPrefix getDev).peerList do
      _ ← rxBranch .setDevFwmarkPeerIter true
      clearPeerEndpointSrcPrefix pid
    _ ← rxBranch .setDevFwmarkPeerIter false
  if ← rxBranch .setDevPort a.listenPort.isSome then
    let ret ← setPortPrefix (a.listenPort.getD 0)
    if ← rxBranch .setDevPortErr (ret != 0) then return ← zero ret
  if ← rxBranch .setDevReplacePeers (flags &&& WGDEVICE_F_REPLACE_PEERS != 0) then peerRemoveAllPrefix
  deviceKeyPrefix a

def wgSetDevicePrefix (a : DeviceAttrs) : MixedM Int := do
  let zero (ret : Int) : MixedM Int := do
    _ ← rxBranch .setDevZeroKey a.privateKey.isSome   -- memzero_explicit
    return ret
  let wg ← liftPrefix (lookupInterface a.device)
  if ← rxBranch .setDevLookupErr (wg matches .error _) then
    let .error e := wg | liftPrefix (invariant "unreachable")
    return ← zero e
  let mut flags : UInt32 := 0
  if ← rxBranch .setDevHasFlags a.flags.isSome then flags := a.flags.getD 0
  if ← rxBranch .setDevBadFlags (flags &&& ~~~WGDEVICE_F_ALL != 0) then return ← zero (-EOPNOTSUPP)
  if ← orPrefix (rxBranch .setDevHasPort a.listenPort.isSome) (rxBranch .setDevHasFwmark a.fwmark.isSome) then
    -- W8: `!net` once the creating namespace exited (netlink.c:517); the
    -- capability half is constant true on this config (section 2.2)
    let denied ← orPrefix (rxBranch .setDevNoNet !(← liftPrefix getDev).creatingNet) (rxBranch .setDevNotCapable false)
    if ← rxBranch .setDevPermErr denied then return ← zero (-EPERM)
  deviceUpdatePrefix a flags


theorem devicePeersPrefix_erases (a : DeviceAttrs) :
    ErasesPrefix (devicePeersPrefix a) (devicePeersSource a) := by
  unfold devicePeersPrefix devicePeersSource
  simp only [bind_assoc, pure_bind]
  repeat' first
    | with_reducible exact setPeerCmdPrefix_erases _
    | with_reducible exact setPortPrefix_erases _
    | with_reducible exact peerRemoveAllPrefix_erases
    | with_reducible exact peerRemovePrefix_erases _
    | with_reducible exact peerPutMixed_erases _
    | with_reducible exact pubkeyLookupPrefix_erases _
    | with_reducible exact clearPeerEndpointSrcPrefix_erases _
    | with_reducible exact precomputeStaticStaticMixed_erases _
    | with_reducible exact expireCurrentPeerKeypairsPrefix_erases _
    | with_reducible exact sendStagedPacketsPrefix_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply andPrefix_erases
    | with_reducible apply orPrefix_erases
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals simp_all

theorem deviceKeyPrefix_erases (a : DeviceAttrs) :
    ErasesPrefix (deviceKeyPrefix a) (deviceKeySource a) := by
  unfold deviceKeyPrefix deviceKeySource
  simp only [bind_assoc, pure_bind]
  repeat' first
    | with_reducible exact devicePeersPrefix_erases _
    | with_reducible exact setPeerCmdPrefix_erases _
    | with_reducible exact setPortPrefix_erases _
    | with_reducible exact peerRemoveAllPrefix_erases
    | with_reducible exact peerRemovePrefix_erases _
    | with_reducible exact peerPutMixed_erases _
    | with_reducible exact pubkeyLookupPrefix_erases _
    | with_reducible exact clearPeerEndpointSrcPrefix_erases _
    | with_reducible exact precomputeStaticStaticMixed_erases _
    | with_reducible exact expireCurrentPeerKeypairsPrefix_erases _
    | with_reducible exact sendStagedPacketsPrefix_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply andPrefix_erases
    | with_reducible apply orPrefix_erases
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals simp_all
  all_goals first | exact erasesPrefix_lift _ | exact pubkeyLookupPrefix_erases _

theorem deviceUpdatePrefix_erases (a : DeviceAttrs) (flags : UInt32) :
    ErasesPrefix (deviceUpdatePrefix a flags) (deviceUpdateSource a flags) := by
  unfold deviceUpdatePrefix deviceUpdateSource
  simp only [bind_assoc, pure_bind]
  repeat' first
    | with_reducible exact devicePeersPrefix_erases _
    | with_reducible exact deviceKeyPrefix_erases _
    | with_reducible exact setPeerCmdPrefix_erases _
    | with_reducible exact setPortPrefix_erases _
    | with_reducible exact peerRemoveAllPrefix_erases
    | with_reducible exact peerRemovePrefix_erases _
    | with_reducible exact peerPutMixed_erases _
    | with_reducible exact pubkeyLookupPrefix_erases _
    | with_reducible exact clearPeerEndpointSrcPrefix_erases _
    | with_reducible exact precomputeStaticStaticMixed_erases _
    | with_reducible exact expireCurrentPeerKeypairsPrefix_erases _
    | with_reducible exact sendStagedPacketsPrefix_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply andPrefix_erases
    | with_reducible apply orPrefix_erases
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals simp_all

theorem wgSetDevicePrefix_erases (a : DeviceAttrs) :
    ErasesPrefix (wgSetDevicePrefix a) (wgSetDevice a) := by
  rw [← wgSetDevice_source]
  unfold wgSetDevicePrefix wgSetDeviceSource
  simp only [bind_assoc, pure_bind]
  repeat' first
    | with_reducible exact devicePeersPrefix_erases _
    | with_reducible exact deviceKeyPrefix_erases _
    | with_reducible exact deviceUpdatePrefix_erases _ _
    | with_reducible exact setPeerCmdPrefix_erases _
    | with_reducible exact setPortPrefix_erases _
    | with_reducible exact peerRemoveAllPrefix_erases
    | with_reducible exact peerRemovePrefix_erases _
    | with_reducible exact peerPutMixed_erases _
    | with_reducible exact pubkeyLookupPrefix_erases _
    | with_reducible exact clearPeerEndpointSrcPrefix_erases _
    | with_reducible exact precomputeStaticStaticMixed_erases _
    | with_reducible exact expireCurrentPeerKeypairsPrefix_erases _
    | with_reducible exact sendStagedPacketsPrefix_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply andPrefix_erases
    | with_reducible apply orPrefix_erases
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals simp_all

structure ConfigurationDeviceContracts (I : List LifetimeEvent → World → Prop) : Prop where
  state : ConfigurationStable I
  precompute : ∀ pid, PrefixPreserves I LifetimeEvent.Safe (precomputeStaticStaticMixed pid)
  index : ∀ owner, PrefixPreserves I LifetimeEvent.Safe (liftPrefix (indexRemove owner))

theorem allocationConfigurationDevice : ConfigurationDeviceContracts AllocationInv :=
  ⟨allocationConfigurationStable, precomputeStaticStaticMixed_allocation, indexRemove_allocation⟩

theorem devicePeersPrefix_preserves (c : AmbientContracts I) (hs : SocketControlStable I)
    (r : ConfigurationPeerContracts I) (d : ConfigurationDeviceContracts I) (a : DeviceAttrs) :
    PrefixPreserves I LifetimeEvent.Safe (devicePeersPrefix a) := by
  unfold devicePeersPrefix
  repeat' first
    | with_reducible exact setPeerCmdPrefix_preserves c r _
    | with_reducible exact setPortPrefix_preserves c hs _
    | with_reducible exact peerRemoveAllPrefix_preserves c r.removal
    | with_reducible exact peerRemovePrefix_preserves c r.removal _
    | with_reducible exact c.peerPut _
    | with_reducible exact pubkeyLookupPrefix_preserves_ambient c _
    | with_reducible exact AmbientContracts.drop (clearPeerEndpointSrcPrefix_spec c (fun _ => True) _)
    | with_reducible exact d.precompute _
    | with_reducible exact expireCurrentPeerKeypairsPrefix_preserves c d.index _
    | with_reducible exact sendStagedPacketsPrefix_preserves_ambient c r.tx _
    | with_reducible exact configurationLift_preserves c d.state _ generation_sameConfiguration
    | with_reducible exact configurationLift_preserves c d.state _ (fwmark_sameConfiguration _)
    | with_reducible exact configurationLift_preserves c d.state _ (setStaticIdentityPrivateKey_sameConfiguration _)
    | with_reducible exact configurationLift_preserves c d.state _ cookiePrecomputeDeviceKeys_sameConfiguration
    | with_reducible exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply AmbientContracts.drop (c.kernel (fun _ => True) _ ?_)
    | with_reducible exact sameKernel_branch _ _
    | with_reducible exact getDev_sameKernel
    | with_reducible exact generatePublic_sameKernel _
    | with_reducible exact lookupInterface_sameKernel _
    | with_reducible apply andPrefix_preserves c.safe
    | with_reducible apply orPrefix_preserves c.safe
    | with_reducible apply PrefixPreserves.forIn _ _ _ c.safe
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals simp_all

theorem deviceKeyPrefix_preserves (c : AmbientContracts I) (hs : SocketControlStable I)
    (r : ConfigurationPeerContracts I) (d : ConfigurationDeviceContracts I) (a : DeviceAttrs) :
    PrefixPreserves I LifetimeEvent.Safe (deviceKeyPrefix a) := by
  unfold deviceKeyPrefix
  repeat' first
    | with_reducible exact devicePeersPrefix_preserves c hs r d _
    | with_reducible exact setPeerCmdPrefix_preserves c r _
    | with_reducible exact setPortPrefix_preserves c hs _
    | with_reducible exact peerRemoveAllPrefix_preserves c r.removal
    | with_reducible exact peerRemovePrefix_preserves c r.removal _
    | with_reducible exact c.peerPut _
    | with_reducible exact pubkeyLookupPrefix_preserves_ambient c _
    | with_reducible exact AmbientContracts.drop (clearPeerEndpointSrcPrefix_spec c (fun _ => True) _)
    | with_reducible exact d.precompute _
    | with_reducible exact expireCurrentPeerKeypairsPrefix_preserves c d.index _
    | with_reducible exact sendStagedPacketsPrefix_preserves_ambient c r.tx _
    | with_reducible exact configurationLift_preserves c d.state _ generation_sameConfiguration
    | with_reducible exact configurationLift_preserves c d.state _ (fwmark_sameConfiguration _)
    | with_reducible exact configurationLift_preserves c d.state _ (setStaticIdentityPrivateKey_sameConfiguration _)
    | with_reducible exact configurationLift_preserves c d.state _ cookiePrecomputeDeviceKeys_sameConfiguration
    | with_reducible exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply AmbientContracts.drop (c.kernel (fun _ => True) _ ?_)
    | with_reducible exact sameKernel_branch _ _
    | with_reducible exact getDev_sameKernel
    | with_reducible exact generatePublic_sameKernel _
    | with_reducible exact lookupInterface_sameKernel _
    | with_reducible apply andPrefix_preserves c.safe
    | with_reducible apply orPrefix_preserves c.safe
    | with_reducible apply PrefixPreserves.forIn _ _ _ c.safe
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals simp_all

theorem deviceUpdatePrefix_preserves (c : AmbientContracts I) (hs : SocketControlStable I)
    (r : ConfigurationPeerContracts I) (d : ConfigurationDeviceContracts I) (a : DeviceAttrs) (flags : UInt32) :
    PrefixPreserves I LifetimeEvent.Safe (deviceUpdatePrefix a flags) := by
  unfold deviceUpdatePrefix
  repeat' first
    | with_reducible exact devicePeersPrefix_preserves c hs r d _
    | with_reducible exact deviceKeyPrefix_preserves c hs r d _
    | with_reducible exact setPeerCmdPrefix_preserves c r _
    | with_reducible exact setPortPrefix_preserves c hs _
    | with_reducible exact peerRemoveAllPrefix_preserves c r.removal
    | with_reducible exact peerRemovePrefix_preserves c r.removal _
    | with_reducible exact c.peerPut _
    | with_reducible exact pubkeyLookupPrefix_preserves_ambient c _
    | with_reducible exact AmbientContracts.drop (clearPeerEndpointSrcPrefix_spec c (fun _ => True) _)
    | with_reducible exact d.precompute _
    | with_reducible exact expireCurrentPeerKeypairsPrefix_preserves c d.index _
    | with_reducible exact sendStagedPacketsPrefix_preserves_ambient c r.tx _
    | with_reducible exact configurationLift_preserves c d.state _ generation_sameConfiguration
    | with_reducible exact configurationLift_preserves c d.state _ (fwmark_sameConfiguration _)
    | with_reducible exact configurationLift_preserves c d.state _ (setStaticIdentityPrivateKey_sameConfiguration _)
    | with_reducible exact configurationLift_preserves c d.state _ cookiePrecomputeDeviceKeys_sameConfiguration
    | with_reducible exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply AmbientContracts.drop (c.kernel (fun _ => True) _ ?_)
    | with_reducible exact sameKernel_branch _ _
    | with_reducible exact getDev_sameKernel
    | with_reducible exact generatePublic_sameKernel _
    | with_reducible exact lookupInterface_sameKernel _
    | with_reducible apply andPrefix_preserves c.safe
    | with_reducible apply orPrefix_preserves c.safe
    | with_reducible apply PrefixPreserves.forIn _ _ _ c.safe
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals simp_all

theorem wgSetDevicePrefix_preserves (c : AmbientContracts I) (hs : SocketControlStable I)
    (r : ConfigurationPeerContracts I) (d : ConfigurationDeviceContracts I) (a : DeviceAttrs) :
    PrefixPreserves I LifetimeEvent.Safe (wgSetDevicePrefix a) := by
  unfold wgSetDevicePrefix
  repeat' first
    | with_reducible exact devicePeersPrefix_preserves c hs r d _
    | with_reducible exact deviceKeyPrefix_preserves c hs r d _
    | with_reducible exact deviceUpdatePrefix_preserves c hs r d _ _
    | with_reducible exact setPeerCmdPrefix_preserves c r _
    | with_reducible exact setPortPrefix_preserves c hs _
    | with_reducible exact peerRemoveAllPrefix_preserves c r.removal
    | with_reducible exact peerRemovePrefix_preserves c r.removal _
    | with_reducible exact c.peerPut _
    | with_reducible exact pubkeyLookupPrefix_preserves_ambient c _
    | with_reducible exact AmbientContracts.drop (clearPeerEndpointSrcPrefix_spec c (fun _ => True) _)
    | with_reducible exact d.precompute _
    | with_reducible exact expireCurrentPeerKeypairsPrefix_preserves c d.index _
    | with_reducible exact sendStagedPacketsPrefix_preserves_ambient c r.tx _
    | with_reducible exact configurationLift_preserves c d.state _ generation_sameConfiguration
    | with_reducible exact configurationLift_preserves c d.state _ (fwmark_sameConfiguration _)
    | with_reducible exact configurationLift_preserves c d.state _ (setStaticIdentityPrivateKey_sameConfiguration _)
    | with_reducible exact configurationLift_preserves c d.state _ cookiePrecomputeDeviceKeys_sameConfiguration
    | with_reducible exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply AmbientContracts.drop (c.kernel (fun _ => True) _ ?_)
    | with_reducible exact sameKernel_branch _ _
    | with_reducible exact getDev_sameKernel
    | with_reducible exact generatePublic_sameKernel _
    | with_reducible exact lookupInterface_sameKernel _
    | with_reducible apply andPrefix_preserves c.safe
    | with_reducible apply orPrefix_preserves c.safe
    | with_reducible apply PrefixPreserves.forIn _ _ _ c.safe
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals simp_all

inductive ConfigurationCall where
  | port (port : Nat)
  | allowedIp (pid : PeerId) (attrs : AllowedIpAttrs)
  | peer (attrs : PeerAttrs)
  | device (attrs : DeviceAttrs)

namespace ConfigurationCall

def original : ConfigurationCall → M Int
  | .port p => setPort p
  | .allowedIp pid attrs => setAllowedip pid attrs
  | .peer attrs => setPeerCmd attrs
  | .device attrs => wgSetDevice attrs

def observed : ConfigurationCall → MixedM Int
  | .port p => setPortPrefix p
  | .allowedIp pid attrs => setAllowedipPrefix pid attrs
  | .peer attrs => setPeerCmdPrefix attrs
  | .device attrs => wgSetDevicePrefix attrs

theorem erases (call : ConfigurationCall) : ErasesPrefix call.observed call.original := by
  cases call with
  | port port => exact setPortPrefix_erases port
  | allowedIp pid attrs => exact setAllowedipPrefix_erases pid attrs
  | peer attrs => exact setPeerCmdPrefix_erases attrs
  | device attrs => exact wgSetDevicePrefix_erases attrs

theorem preserves_ambient (c : AmbientContracts I) (hs : SocketControlStable I)
    (r : ConfigurationPeerContracts I) (d : ConfigurationDeviceContracts I) (call : ConfigurationCall) :
    PrefixPreserves I LifetimeEvent.Safe call.observed := by
  cases call with
  | port port => exact setPortPrefix_preserves c hs port
  | allowedIp pid attrs => exact setAllowedipPrefix_preserves c r.nodes pid attrs
  | peer attrs => exact setPeerCmdPrefix_preserves c r attrs
  | device attrs => exact wgSetDevicePrefix_preserves c hs r d attrs

theorem allocation (call : ConfigurationCall) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe call.observed :=
  call.preserves_ambient allocationAmbient allocationSocketControlStable allocationConfigurationPeer allocationConfigurationDevice

end ConfigurationCall
end Leanux.Proofs.WG.Lifetimes
