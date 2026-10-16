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
    let some key := a.privateKey | liftWGPrefix (invariant "unreachable")
    -- `!crypto_memneq(static_private, private_key)`: the stored key is clamped
    if !(← rxBranch .setDevKeyUnchanged ((← liftWGPrefix getDev).staticIdentity.staticPrivate == key)) then
      -- remove the peer whose public key the device is about to take
      let (pub, ok) ← liftWGPrefix (generatePublic key)
      if ← rxBranch .setDevGenPublic ok then
        let some pub := pub | liftWGPrefix (invariant "a generated public key without a write")
        let peer ← pubkeyLookupPrefix pub
        if ← rxBranch .setDevOldPeer peer.isSome then
          peerPutMixed peer
          peerRemovePrefix peer
      let d ← liftWGPrefix getDev
      let sendStaged ← andPrefix (rxBranch .setDevSendStagedNoIdentity !d.staticIdentity.hasIdentity)
        (rxBranch .setDevSendStagedRunning d.running)
      liftWGPrefix (setStaticIdentityPrivateKey key)
      let hasIdentity := (← liftWGPrefix getDev).staticIdentity.hasIdentity
      let sendStaged ← andPrefix (rxBranch .setDevSendStagedKept sendStaged) (rxBranch .setDevSendStagedHasIdentity hasIdentity)
      liftWGPrefix cookiePrecomputeDeviceKeys
      for pid in (← liftWGPrefix getDev).peerList do
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
  liftWGPrefix (modifyDev fun d => { d with deviceUpdateGen := d.deviceUpdateGen + 1 })
  if ← rxBranch .setDevFwmark a.fwmark.isSome then
    liftWGPrefix (modifyDev fun d => { d with fwmark := a.fwmark.getD 0 })
    for pid in (← liftWGPrefix getDev).peerList do
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
  let wg ← liftWGPrefix (lookupInterface a.device)
  if ← rxBranch .setDevLookupErr (wg matches .error _) then
    let .error e := wg | liftWGPrefix (invariant "unreachable")
    return ← zero e
  let mut flags : UInt32 := 0
  if ← rxBranch .setDevHasFlags a.flags.isSome then flags := a.flags.getD 0
  if ← rxBranch .setDevBadFlags (flags &&& ~~~WGDEVICE_F_ALL != 0) then return ← zero (-EOPNOTSUPP)
  if ← orPrefix (rxBranch .setDevHasPort a.listenPort.isSome) (rxBranch .setDevHasFwmark a.fwmark.isSome) then
    -- W8: `!net` once the creating namespace exited (netlink.c:517); the
    -- capability half is constant true on this config (section 2.2)
    let denied ← orPrefix (rxBranch .setDevNoNet !(← liftWGPrefix getDev).creatingNet) (rxBranch .setDevNotCapable false)
    if ← rxBranch .setDevPermErr denied then return ← zero (-EPERM)
  deviceUpdatePrefix a flags


theorem devicePeersPrefix_erases (a : DeviceAttrs) :
    ErasesStatePrefix (devicePeersPrefix a) (devicePeersSource a) := by
  unfold devicePeersPrefix devicePeersSource
  repeat' first
    | contradiction
    | maintenance_impossible_match
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_erases_bind
    | (maintenance_head setPeerCmdPrefix; exact setPeerCmdPrefix_erases _)
    | (maintenance_head setPortPrefix; exact setPortPrefix_erases _)
    | (maintenance_head peerRemoveAllPrefix; exact peerRemoveAllPrefix_erases )
    | (maintenance_head peerRemovePrefix; exact peerRemovePrefix_erases _)
    | (maintenance_head peerPutMixed; exact peerPutMixed_erases _)
    | (maintenance_head pubkeyLookupPrefix; exact pubkeyLookupPrefix_erases _)
    | (maintenance_head clearPeerEndpointSrcPrefix; exact clearPeerEndpointSrcPrefix_erases _)
    | (maintenance_head precomputeStaticStaticMixed; exact precomputeStaticStaticMixed_erases _)
    | (maintenance_head expireCurrentPeerKeypairsPrefix; exact expireCurrentPeerKeypairsPrefix_erases _)
    | (maintenance_head sendStagedPacketsPrefix; exact sendStagedPacketsPrefix_erases _)
    | (maintenance_head andPrefix; unfold andPrefix WG.andM)
    | (maintenance_head orPrefix; unfold orPrefix WG.orM)
    | (maintenance_head rxBranch; unfold rxBranch)
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | (maintenance_head ForIn.forIn; apply erasesStatePrefix_forIn)
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro
    | rfl

theorem deviceKeyPrefix_erases (a : DeviceAttrs) :
    ErasesStatePrefix (deviceKeyPrefix a) (deviceKeySource a) := by
  unfold deviceKeyPrefix deviceKeySource
  repeat' first
    | contradiction
    | maintenance_impossible_match
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_erases_bind
    | (maintenance_head devicePeersPrefix; exact devicePeersPrefix_erases _)
    | (maintenance_head setPeerCmdPrefix; exact setPeerCmdPrefix_erases _)
    | (maintenance_head setPortPrefix; exact setPortPrefix_erases _)
    | (maintenance_head peerRemoveAllPrefix; exact peerRemoveAllPrefix_erases )
    | (maintenance_head peerRemovePrefix; exact peerRemovePrefix_erases _)
    | (maintenance_head peerPutMixed; exact peerPutMixed_erases _)
    | (maintenance_head pubkeyLookupPrefix; exact pubkeyLookupPrefix_erases _)
    | (maintenance_head clearPeerEndpointSrcPrefix; exact clearPeerEndpointSrcPrefix_erases _)
    | (maintenance_head precomputeStaticStaticMixed; exact precomputeStaticStaticMixed_erases _)
    | (maintenance_head expireCurrentPeerKeypairsPrefix; exact expireCurrentPeerKeypairsPrefix_erases _)
    | (maintenance_head sendStagedPacketsPrefix; exact sendStagedPacketsPrefix_erases _)
    | (maintenance_head andPrefix; unfold andPrefix WG.andM)
    | (maintenance_head orPrefix; unfold orPrefix WG.orM)
    | (maintenance_head rxBranch; unfold rxBranch)
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | (maintenance_head ForIn.forIn; apply erasesStatePrefix_forIn)
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro
    | rfl

theorem deviceUpdatePrefix_erases (a : DeviceAttrs) (flags : UInt32) :
    ErasesStatePrefix (deviceUpdatePrefix a flags) (deviceUpdateSource a flags) := by
  unfold deviceUpdatePrefix deviceUpdateSource
  repeat' first
    | contradiction
    | maintenance_impossible_match
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_erases_bind
    | (maintenance_head devicePeersPrefix; exact devicePeersPrefix_erases _)
    | (maintenance_head deviceKeyPrefix; exact deviceKeyPrefix_erases _)
    | (maintenance_head setPeerCmdPrefix; exact setPeerCmdPrefix_erases _)
    | (maintenance_head setPortPrefix; exact setPortPrefix_erases _)
    | (maintenance_head peerRemoveAllPrefix; exact peerRemoveAllPrefix_erases )
    | (maintenance_head peerRemovePrefix; exact peerRemovePrefix_erases _)
    | (maintenance_head peerPutMixed; exact peerPutMixed_erases _)
    | (maintenance_head pubkeyLookupPrefix; exact pubkeyLookupPrefix_erases _)
    | (maintenance_head clearPeerEndpointSrcPrefix; exact clearPeerEndpointSrcPrefix_erases _)
    | (maintenance_head precomputeStaticStaticMixed; exact precomputeStaticStaticMixed_erases _)
    | (maintenance_head expireCurrentPeerKeypairsPrefix; exact expireCurrentPeerKeypairsPrefix_erases _)
    | (maintenance_head sendStagedPacketsPrefix; exact sendStagedPacketsPrefix_erases _)
    | (maintenance_head andPrefix; unfold andPrefix WG.andM)
    | (maintenance_head orPrefix; unfold orPrefix WG.orM)
    | (maintenance_head rxBranch; unfold rxBranch)
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | (maintenance_head ForIn.forIn; apply erasesStatePrefix_forIn)
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro
    | rfl

theorem wgSetDevicePrefix_erases (a : DeviceAttrs) :
    ErasesStatePrefix (wgSetDevicePrefix a) (wgSetDevice a) := by
  rw [← wgSetDevice_source]
  unfold wgSetDevicePrefix wgSetDeviceSource
  repeat' first
    | contradiction
    | maintenance_impossible_match
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_erases_bind
    | (maintenance_head devicePeersPrefix; exact devicePeersPrefix_erases _)
    | (maintenance_head deviceKeyPrefix; exact deviceKeyPrefix_erases _)
    | (maintenance_head deviceUpdatePrefix; exact deviceUpdatePrefix_erases _ _)
    | (maintenance_head setPeerCmdPrefix; exact setPeerCmdPrefix_erases _)
    | (maintenance_head setPortPrefix; exact setPortPrefix_erases _)
    | (maintenance_head peerRemoveAllPrefix; exact peerRemoveAllPrefix_erases )
    | (maintenance_head peerRemovePrefix; exact peerRemovePrefix_erases _)
    | (maintenance_head peerPutMixed; exact peerPutMixed_erases _)
    | (maintenance_head pubkeyLookupPrefix; exact pubkeyLookupPrefix_erases _)
    | (maintenance_head clearPeerEndpointSrcPrefix; exact clearPeerEndpointSrcPrefix_erases _)
    | (maintenance_head precomputeStaticStaticMixed; exact precomputeStaticStaticMixed_erases _)
    | (maintenance_head expireCurrentPeerKeypairsPrefix; exact expireCurrentPeerKeypairsPrefix_erases _)
    | (maintenance_head sendStagedPacketsPrefix; exact sendStagedPacketsPrefix_erases _)
    | (maintenance_head andPrefix; unfold andPrefix WG.andM)
    | (maintenance_head orPrefix; unfold orPrefix WG.orM)
    | (maintenance_head rxBranch; unfold rxBranch)
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | (maintenance_head ForIn.forIn; apply erasesStatePrefix_forIn)
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro
    | rfl

structure ConfigurationDeviceContracts (I : List LifetimeEvent → WGWorld → Prop) : Prop where
  state : ConfigurationStable I
  precompute : ∀ pid, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (precomputeStaticStaticMixed pid)
  index : ∀ owner, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe
    (liftWGPrefix (liftIndex (indexRemove owner)))

structure ProductConfigurationDeviceContracts (I : List LifetimeEvent → World → Prop) : Prop where
  state : ProductConfigurationStable I
  precompute : ∀ pid, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (precomputeStaticStaticMixed pid))
  index : ∀ owner, PrefixPreserves I LifetimeEvent.Safe
    (liftWGObserver (liftWGPrefix (liftIndex (indexRemove owner))))

theorem allocationConfigurationDevice : ConfigurationDeviceContracts AllocationInv :=
  ⟨allocationConfigurationStable, precomputeStaticStaticMixed_allocation, indexRemove_allocation⟩

theorem devicePeersPrefix_preserves (c : AmbientContracts I) (_hs : SocketControlStable I)
    (r : ConfigurationPeerContracts I) (_d : ConfigurationDeviceContracts I) (a : DeviceAttrs) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (devicePeersPrefix a) := by
  change StatePrefixEnsures _ _ _ _
  unfold devicePeersPrefix
  repeat' first
    | (maintenance_head setPeerCmdPrefix; exact setPeerCmdPrefix_preserves c r _)
    | (maintenance_head setPortPrefix; exact setPortPrefix_preserves c _hs _)
    | (maintenance_head peerRemoveAllPrefix; exact peerRemoveAllPrefix_preserves c r.removal)
    | (maintenance_head peerRemovePrefix; exact peerRemovePrefix_preserves c r.removal _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head pubkeyLookupPrefix; exact pubkeyLookupPrefix_preserves_ambient c _)
    | (maintenance_head clearPeerEndpointSrcPrefix; exact AmbientContracts.drop (clearPeerEndpointSrcPrefix_spec c (fun _ => True) _))
    | (maintenance_head precomputeStaticStaticMixed; exact _d.precompute _)
    | (maintenance_head expireCurrentPeerKeypairsPrefix; exact expireCurrentPeerKeypairsPrefix_preserves c _d.index _)
    | (maintenance_head sendStagedPacketsPrefix; exact sendStagedPacketsPrefix_preserves_ambient c r.tx _)
    | (maintenance_lift_action_head modifyDev; exact configurationLift_preserves_native c _d.state _ (generation_sameConfiguration.factor WGOwnedView.toWGStoreView))
    | (maintenance_lift_action_head modifyDev; exact configurationLift_preserves_native c _d.state _ ((fwmark_sameConfiguration _).factor WGOwnedView.toWGStoreView))
    | (maintenance_lift_action_head setStaticIdentityPrivateKey; exact configurationLift_preserves_native c _d.state _ ((setStaticIdentityPrivateKey_sameConfiguration _).factor WGOwnedView.toWGStoreView))
    | (maintenance_lift_action_head cookiePrecomputeDeviceKeys; exact configurationLift_preserves_native c _d.state _ (cookiePrecomputeDeviceKeys_sameConfiguration.factor WGOwnedView.toWGStoreView))
    | (maintenance_lift_action_head getDev; exact AmbientContracts.drop (c.store (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head generatePublic; exact AmbientContracts.drop (c.store (fun _ => True) _ ((generatePublic_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head lookupInterface; exact AmbientContracts.drop (c.store (fun _ => True) _ ((lookupInterface_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head branch; exact AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.branch _ _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head invariant; exact AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.invariant _) (fun w => wgStoreView w = initial))))
    | (maintenance_head rxBranch; unfold rxBranch)
    | (maintenance_head andPrefix; unfold andPrefix)
    | (maintenance_head orPrefix; unfold orPrefix)
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head ForIn.forIn; apply StatePrefixEnsures.forInInvariant _ _ _ (fun _ h w _ => I h w) LifetimeEvent.Safe (fun _ h w _ hi => c.safe h w hi); intro x b; change StatePrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem deviceKeyPrefix_preserves (c : AmbientContracts I) (hs : SocketControlStable I)
    (r : ConfigurationPeerContracts I) (d : ConfigurationDeviceContracts I) (a : DeviceAttrs) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (deviceKeyPrefix a) := by
  change StatePrefixEnsures _ _ _ _
  unfold deviceKeyPrefix
  repeat' first
    | (maintenance_head devicePeersPrefix; exact devicePeersPrefix_preserves c hs r d _)
    | (maintenance_head setPeerCmdPrefix; exact setPeerCmdPrefix_preserves c r _)
    | (maintenance_head setPortPrefix; exact setPortPrefix_preserves c hs _)
    | (maintenance_head peerRemoveAllPrefix; exact peerRemoveAllPrefix_preserves c r.removal)
    | (maintenance_head peerRemovePrefix; exact peerRemovePrefix_preserves c r.removal _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head pubkeyLookupPrefix; exact pubkeyLookupPrefix_preserves_ambient c _)
    | (maintenance_head clearPeerEndpointSrcPrefix; exact AmbientContracts.drop (clearPeerEndpointSrcPrefix_spec c (fun _ => True) _))
    | (maintenance_head precomputeStaticStaticMixed; exact d.precompute _)
    | (maintenance_head expireCurrentPeerKeypairsPrefix; exact expireCurrentPeerKeypairsPrefix_preserves c d.index _)
    | (maintenance_head sendStagedPacketsPrefix; exact sendStagedPacketsPrefix_preserves_ambient c r.tx _)
    | (maintenance_lift_action_head modifyDev; exact configurationLift_preserves_native c d.state _ (generation_sameConfiguration.factor WGOwnedView.toWGStoreView))
    | (maintenance_lift_action_head modifyDev; exact configurationLift_preserves_native c d.state _ ((fwmark_sameConfiguration _).factor WGOwnedView.toWGStoreView))
    | (maintenance_lift_action_head setStaticIdentityPrivateKey; exact configurationLift_preserves_native c d.state _ ((setStaticIdentityPrivateKey_sameConfiguration _).factor WGOwnedView.toWGStoreView))
    | (maintenance_lift_action_head cookiePrecomputeDeviceKeys; exact configurationLift_preserves_native c d.state _ (cookiePrecomputeDeviceKeys_sameConfiguration.factor WGOwnedView.toWGStoreView))
    | (maintenance_lift_action_head getDev; exact AmbientContracts.drop (c.store (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head generatePublic; exact AmbientContracts.drop (c.store (fun _ => True) _ ((generatePublic_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head lookupInterface; exact AmbientContracts.drop (c.store (fun _ => True) _ ((lookupInterface_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head branch; exact AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.branch _ _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head invariant; exact AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.invariant _) (fun w => wgStoreView w = initial))))
    | (maintenance_head rxBranch; unfold rxBranch)
    | (maintenance_head andPrefix; unfold andPrefix)
    | (maintenance_head orPrefix; unfold orPrefix)
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head ForIn.forIn; apply StatePrefixEnsures.forInInvariant _ _ _ (fun _ h w _ => I h w) LifetimeEvent.Safe (fun _ h w _ hi => c.safe h w hi); intro x b; change StatePrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem deviceUpdatePrefix_preserves (c : AmbientContracts I) (hs : SocketControlStable I)
    (r : ConfigurationPeerContracts I) (d : ConfigurationDeviceContracts I) (a : DeviceAttrs) (flags : UInt32) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (deviceUpdatePrefix a flags) := by
  change StatePrefixEnsures _ _ _ _
  unfold deviceUpdatePrefix
  repeat' first
    | (maintenance_head devicePeersPrefix; exact devicePeersPrefix_preserves c hs r d _)
    | (maintenance_head deviceKeyPrefix; exact deviceKeyPrefix_preserves c hs r d _)
    | (maintenance_head setPeerCmdPrefix; exact setPeerCmdPrefix_preserves c r _)
    | (maintenance_head setPortPrefix; exact setPortPrefix_preserves c hs _)
    | (maintenance_head peerRemoveAllPrefix; exact peerRemoveAllPrefix_preserves c r.removal)
    | (maintenance_head peerRemovePrefix; exact peerRemovePrefix_preserves c r.removal _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head pubkeyLookupPrefix; exact pubkeyLookupPrefix_preserves_ambient c _)
    | (maintenance_head clearPeerEndpointSrcPrefix; exact AmbientContracts.drop (clearPeerEndpointSrcPrefix_spec c (fun _ => True) _))
    | (maintenance_head precomputeStaticStaticMixed; exact d.precompute _)
    | (maintenance_head expireCurrentPeerKeypairsPrefix; exact expireCurrentPeerKeypairsPrefix_preserves c d.index _)
    | (maintenance_head sendStagedPacketsPrefix; exact sendStagedPacketsPrefix_preserves_ambient c r.tx _)
    | (maintenance_lift_action_head modifyDev; exact configurationLift_preserves_native c d.state _ (generation_sameConfiguration.factor WGOwnedView.toWGStoreView))
    | (maintenance_lift_action_head modifyDev; exact configurationLift_preserves_native c d.state _ ((fwmark_sameConfiguration _).factor WGOwnedView.toWGStoreView))
    | (maintenance_lift_action_head setStaticIdentityPrivateKey; exact configurationLift_preserves_native c d.state _ ((setStaticIdentityPrivateKey_sameConfiguration _).factor WGOwnedView.toWGStoreView))
    | (maintenance_lift_action_head cookiePrecomputeDeviceKeys; exact configurationLift_preserves_native c d.state _ (cookiePrecomputeDeviceKeys_sameConfiguration.factor WGOwnedView.toWGStoreView))
    | (maintenance_lift_action_head getDev; exact AmbientContracts.drop (c.store (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head generatePublic; exact AmbientContracts.drop (c.store (fun _ => True) _ ((generatePublic_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head lookupInterface; exact AmbientContracts.drop (c.store (fun _ => True) _ ((lookupInterface_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head branch; exact AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.branch _ _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head invariant; exact AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.invariant _) (fun w => wgStoreView w = initial))))
    | (maintenance_head rxBranch; unfold rxBranch)
    | (maintenance_head andPrefix; unfold andPrefix)
    | (maintenance_head orPrefix; unfold orPrefix)
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head ForIn.forIn; apply StatePrefixEnsures.forInInvariant _ _ _ (fun _ h w _ => I h w) LifetimeEvent.Safe (fun _ h w _ hi => c.safe h w hi); intro x b; change StatePrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem wgSetDevicePrefix_preserves (c : AmbientContracts I) (hs : SocketControlStable I)
    (r : ConfigurationPeerContracts I) (d : ConfigurationDeviceContracts I) (a : DeviceAttrs) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (wgSetDevicePrefix a) := by
  change StatePrefixEnsures _ _ _ _
  unfold wgSetDevicePrefix
  repeat' first
    | (maintenance_head devicePeersPrefix; exact devicePeersPrefix_preserves c hs r d _)
    | (maintenance_head deviceKeyPrefix; exact deviceKeyPrefix_preserves c hs r d _)
    | (maintenance_head deviceUpdatePrefix; exact deviceUpdatePrefix_preserves c hs r d _ _)
    | (maintenance_head setPeerCmdPrefix; exact setPeerCmdPrefix_preserves c r _)
    | (maintenance_head setPortPrefix; exact setPortPrefix_preserves c hs _)
    | (maintenance_head peerRemoveAllPrefix; exact peerRemoveAllPrefix_preserves c r.removal)
    | (maintenance_head peerRemovePrefix; exact peerRemovePrefix_preserves c r.removal _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head pubkeyLookupPrefix; exact pubkeyLookupPrefix_preserves_ambient c _)
    | (maintenance_head clearPeerEndpointSrcPrefix; exact AmbientContracts.drop (clearPeerEndpointSrcPrefix_spec c (fun _ => True) _))
    | (maintenance_head precomputeStaticStaticMixed; exact d.precompute _)
    | (maintenance_head expireCurrentPeerKeypairsPrefix; exact expireCurrentPeerKeypairsPrefix_preserves c d.index _)
    | (maintenance_head sendStagedPacketsPrefix; exact sendStagedPacketsPrefix_preserves_ambient c r.tx _)
    | (maintenance_lift_action_head modifyDev; exact configurationLift_preserves_native c d.state _ (generation_sameConfiguration.factor WGOwnedView.toWGStoreView))
    | (maintenance_lift_action_head modifyDev; exact configurationLift_preserves_native c d.state _ ((fwmark_sameConfiguration _).factor WGOwnedView.toWGStoreView))
    | (maintenance_lift_action_head setStaticIdentityPrivateKey; exact configurationLift_preserves_native c d.state _ ((setStaticIdentityPrivateKey_sameConfiguration _).factor WGOwnedView.toWGStoreView))
    | (maintenance_lift_action_head cookiePrecomputeDeviceKeys; exact configurationLift_preserves_native c d.state _ (cookiePrecomputeDeviceKeys_sameConfiguration.factor WGOwnedView.toWGStoreView))
    | (maintenance_lift_action_head getDev; exact AmbientContracts.drop (c.store (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head generatePublic; exact AmbientContracts.drop (c.store (fun _ => True) _ ((generatePublic_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head lookupInterface; exact AmbientContracts.drop (c.store (fun _ => True) _ ((lookupInterface_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head branch; exact AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.branch _ _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head invariant; exact AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.invariant _) (fun w => wgStoreView w = initial))))
    | (maintenance_head rxBranch; unfold rxBranch)
    | (maintenance_head andPrefix; unfold andPrefix)
    | (maintenance_head orPrefix; unfold orPrefix)
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head ForIn.forIn; apply StatePrefixEnsures.forInInvariant _ _ _ (fun _ h w _ => I h w) LifetimeEvent.Safe (fun _ h w _ hi => c.safe h w hi); intro x b; change StatePrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem devicePeersPrefix_preserves_product (c : ProductAmbientContracts I) (_hs : ProductSocketControlStable I)
    (r : ProductConfigurationPeerContracts I) (_d : ProductConfigurationDeviceContracts I) (a : DeviceAttrs) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (devicePeersPrefix a)) := by
  change PrefixEnsures _ _ _ _
  unfold devicePeersPrefix
  repeat' first
    | (first | rw [liftWGObserver_bind] | rw [liftWGObserver_pure] | rw [liftWGObserver_forIn] | rw [apply_ite])
    | (maintenance_head setPeerCmdPrefix; exact setPeerCmdPrefix_preserves_product c r _)
    | (maintenance_head setPortPrefix; exact setPortPrefix_preserves_product c _hs _)
    | (maintenance_head peerRemoveAllPrefix; exact peerRemoveAllPrefix_preserves_product c r.removal)
    | (maintenance_head peerRemovePrefix; exact peerRemovePrefix_preserves_product c r.removal _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head pubkeyLookupPrefix; exact pubkeyLookupPrefix_preserves_product c _)
    | (maintenance_head clearPeerEndpointSrcPrefix; exact ProductAmbientContracts.drop (clearPeerEndpointSrcPrefix_spec_product c (fun _ => True) _))
    | (maintenance_head precomputeStaticStaticMixed; exact _d.precompute _)
    | (maintenance_head expireCurrentPeerKeypairsPrefix; exact expireCurrentPeerKeypairsPrefix_preserves_product c _d.index _)
    | (maintenance_head sendStagedPacketsPrefix; exact sendStagedPacketsPrefix_preserves_product c r.tx _)
    | (maintenance_lift_action_head modifyDev; exact configurationLift_native_product c _d.state _ (generation_sameConfiguration.factor WGOwnedView.toWGStoreView))
    | (maintenance_lift_action_head modifyDev; exact configurationLift_native_product c _d.state _ ((fwmark_sameConfiguration _).factor WGOwnedView.toWGStoreView))
    | (maintenance_lift_action_head setStaticIdentityPrivateKey; exact configurationLift_native_product c _d.state _ ((setStaticIdentityPrivateKey_sameConfiguration _).factor WGOwnedView.toWGStoreView))
    | (maintenance_lift_action_head cookiePrecomputeDeviceKeys; exact configurationLift_native_product c _d.state _ (cookiePrecomputeDeviceKeys_sameConfiguration.factor WGOwnedView.toWGStoreView))
    | (maintenance_lift_action_head getDev; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head generatePublic; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((generatePublic_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head lookupInterface; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((lookupInterface_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head branch; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.branch _ _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head invariant; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.invariant _) (fun w => wgStoreView w = initial))))
    | (maintenance_head rxBranch; unfold rxBranch)
    | (maintenance_head andPrefix; unfold andPrefix)
    | (maintenance_head orPrefix; unfold orPrefix)
    | (maintenance_head Pure.pure; exact PrefixPreserves.pure c.safe _)
    | (maintenance_head ForIn.forIn; apply PrefixPreserves.forIn _ _ _ c.safe; intro x b; change PrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem deviceKeyPrefix_preserves_product (c : ProductAmbientContracts I) (hs : ProductSocketControlStable I)
    (r : ProductConfigurationPeerContracts I) (d : ProductConfigurationDeviceContracts I) (a : DeviceAttrs) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (deviceKeyPrefix a)) := by
  change PrefixEnsures _ _ _ _
  unfold deviceKeyPrefix
  repeat' first
    | (first | rw [liftWGObserver_bind] | rw [liftWGObserver_pure] | rw [liftWGObserver_forIn] | rw [apply_ite])
    | (maintenance_head devicePeersPrefix; exact devicePeersPrefix_preserves_product c hs r d _)
    | (maintenance_head setPeerCmdPrefix; exact setPeerCmdPrefix_preserves_product c r _)
    | (maintenance_head setPortPrefix; exact setPortPrefix_preserves_product c hs _)
    | (maintenance_head peerRemoveAllPrefix; exact peerRemoveAllPrefix_preserves_product c r.removal)
    | (maintenance_head peerRemovePrefix; exact peerRemovePrefix_preserves_product c r.removal _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head pubkeyLookupPrefix; exact pubkeyLookupPrefix_preserves_product c _)
    | (maintenance_head clearPeerEndpointSrcPrefix; exact ProductAmbientContracts.drop (clearPeerEndpointSrcPrefix_spec_product c (fun _ => True) _))
    | (maintenance_head precomputeStaticStaticMixed; exact d.precompute _)
    | (maintenance_head expireCurrentPeerKeypairsPrefix; exact expireCurrentPeerKeypairsPrefix_preserves_product c d.index _)
    | (maintenance_head sendStagedPacketsPrefix; exact sendStagedPacketsPrefix_preserves_product c r.tx _)
    | (maintenance_lift_action_head modifyDev; exact configurationLift_native_product c d.state _ (generation_sameConfiguration.factor WGOwnedView.toWGStoreView))
    | (maintenance_lift_action_head modifyDev; exact configurationLift_native_product c d.state _ ((fwmark_sameConfiguration _).factor WGOwnedView.toWGStoreView))
    | (maintenance_lift_action_head setStaticIdentityPrivateKey; exact configurationLift_native_product c d.state _ ((setStaticIdentityPrivateKey_sameConfiguration _).factor WGOwnedView.toWGStoreView))
    | (maintenance_lift_action_head cookiePrecomputeDeviceKeys; exact configurationLift_native_product c d.state _ (cookiePrecomputeDeviceKeys_sameConfiguration.factor WGOwnedView.toWGStoreView))
    | (maintenance_lift_action_head getDev; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head generatePublic; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((generatePublic_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head lookupInterface; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((lookupInterface_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head branch; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.branch _ _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head invariant; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.invariant _) (fun w => wgStoreView w = initial))))
    | (maintenance_head rxBranch; unfold rxBranch)
    | (maintenance_head andPrefix; unfold andPrefix)
    | (maintenance_head orPrefix; unfold orPrefix)
    | (maintenance_head Pure.pure; exact PrefixPreserves.pure c.safe _)
    | (maintenance_head ForIn.forIn; apply PrefixPreserves.forIn _ _ _ c.safe; intro x b; change PrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem deviceUpdatePrefix_preserves_product (c : ProductAmbientContracts I) (hs : ProductSocketControlStable I)
    (r : ProductConfigurationPeerContracts I) (d : ProductConfigurationDeviceContracts I) (a : DeviceAttrs) (flags : UInt32) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (deviceUpdatePrefix a flags)) := by
  change PrefixEnsures _ _ _ _
  unfold deviceUpdatePrefix
  repeat' first
    | (first | rw [liftWGObserver_bind] | rw [liftWGObserver_pure] | rw [liftWGObserver_forIn] | rw [apply_ite])
    | (maintenance_head devicePeersPrefix; exact devicePeersPrefix_preserves_product c hs r d _)
    | (maintenance_head deviceKeyPrefix; exact deviceKeyPrefix_preserves_product c hs r d _)
    | (maintenance_head setPeerCmdPrefix; exact setPeerCmdPrefix_preserves_product c r _)
    | (maintenance_head setPortPrefix; exact setPortPrefix_preserves_product c hs _)
    | (maintenance_head peerRemoveAllPrefix; exact peerRemoveAllPrefix_preserves_product c r.removal)
    | (maintenance_head peerRemovePrefix; exact peerRemovePrefix_preserves_product c r.removal _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head pubkeyLookupPrefix; exact pubkeyLookupPrefix_preserves_product c _)
    | (maintenance_head clearPeerEndpointSrcPrefix; exact ProductAmbientContracts.drop (clearPeerEndpointSrcPrefix_spec_product c (fun _ => True) _))
    | (maintenance_head precomputeStaticStaticMixed; exact d.precompute _)
    | (maintenance_head expireCurrentPeerKeypairsPrefix; exact expireCurrentPeerKeypairsPrefix_preserves_product c d.index _)
    | (maintenance_head sendStagedPacketsPrefix; exact sendStagedPacketsPrefix_preserves_product c r.tx _)
    | (maintenance_lift_action_head modifyDev; exact configurationLift_native_product c d.state _ (generation_sameConfiguration.factor WGOwnedView.toWGStoreView))
    | (maintenance_lift_action_head modifyDev; exact configurationLift_native_product c d.state _ ((fwmark_sameConfiguration _).factor WGOwnedView.toWGStoreView))
    | (maintenance_lift_action_head setStaticIdentityPrivateKey; exact configurationLift_native_product c d.state _ ((setStaticIdentityPrivateKey_sameConfiguration _).factor WGOwnedView.toWGStoreView))
    | (maintenance_lift_action_head cookiePrecomputeDeviceKeys; exact configurationLift_native_product c d.state _ (cookiePrecomputeDeviceKeys_sameConfiguration.factor WGOwnedView.toWGStoreView))
    | (maintenance_lift_action_head getDev; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head generatePublic; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((generatePublic_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head lookupInterface; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((lookupInterface_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head branch; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.branch _ _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head invariant; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.invariant _) (fun w => wgStoreView w = initial))))
    | (maintenance_head rxBranch; unfold rxBranch)
    | (maintenance_head andPrefix; unfold andPrefix)
    | (maintenance_head orPrefix; unfold orPrefix)
    | (maintenance_head Pure.pure; exact PrefixPreserves.pure c.safe _)
    | (maintenance_head ForIn.forIn; apply PrefixPreserves.forIn _ _ _ c.safe; intro x b; change PrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem wgSetDevicePrefix_preserves_product (c : ProductAmbientContracts I) (hs : ProductSocketControlStable I)
    (r : ProductConfigurationPeerContracts I) (d : ProductConfigurationDeviceContracts I) (a : DeviceAttrs) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (wgSetDevicePrefix a)) := by
  change PrefixEnsures _ _ _ _
  unfold wgSetDevicePrefix
  repeat' first
    | (first | rw [liftWGObserver_bind] | rw [liftWGObserver_pure] | rw [liftWGObserver_forIn] | rw [apply_ite])
    | (maintenance_head devicePeersPrefix; exact devicePeersPrefix_preserves_product c hs r d _)
    | (maintenance_head deviceKeyPrefix; exact deviceKeyPrefix_preserves_product c hs r d _)
    | (maintenance_head deviceUpdatePrefix; exact deviceUpdatePrefix_preserves_product c hs r d _ _)
    | (maintenance_head setPeerCmdPrefix; exact setPeerCmdPrefix_preserves_product c r _)
    | (maintenance_head setPortPrefix; exact setPortPrefix_preserves_product c hs _)
    | (maintenance_head peerRemoveAllPrefix; exact peerRemoveAllPrefix_preserves_product c r.removal)
    | (maintenance_head peerRemovePrefix; exact peerRemovePrefix_preserves_product c r.removal _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head pubkeyLookupPrefix; exact pubkeyLookupPrefix_preserves_product c _)
    | (maintenance_head clearPeerEndpointSrcPrefix; exact ProductAmbientContracts.drop (clearPeerEndpointSrcPrefix_spec_product c (fun _ => True) _))
    | (maintenance_head precomputeStaticStaticMixed; exact d.precompute _)
    | (maintenance_head expireCurrentPeerKeypairsPrefix; exact expireCurrentPeerKeypairsPrefix_preserves_product c d.index _)
    | (maintenance_head sendStagedPacketsPrefix; exact sendStagedPacketsPrefix_preserves_product c r.tx _)
    | (maintenance_lift_action_head modifyDev; exact configurationLift_native_product c d.state _ (generation_sameConfiguration.factor WGOwnedView.toWGStoreView))
    | (maintenance_lift_action_head modifyDev; exact configurationLift_native_product c d.state _ ((fwmark_sameConfiguration _).factor WGOwnedView.toWGStoreView))
    | (maintenance_lift_action_head setStaticIdentityPrivateKey; exact configurationLift_native_product c d.state _ ((setStaticIdentityPrivateKey_sameConfiguration _).factor WGOwnedView.toWGStoreView))
    | (maintenance_lift_action_head cookiePrecomputeDeviceKeys; exact configurationLift_native_product c d.state _ (cookiePrecomputeDeviceKeys_sameConfiguration.factor WGOwnedView.toWGStoreView))
    | (maintenance_lift_action_head getDev; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head generatePublic; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((generatePublic_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head lookupInterface; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((lookupInterface_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head branch; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.branch _ _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head invariant; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.invariant _) (fun w => wgStoreView w = initial))))
    | (maintenance_head rxBranch; unfold rxBranch)
    | (maintenance_head andPrefix; unfold andPrefix)
    | (maintenance_head orPrefix; unfold orPrefix)
    | (maintenance_head Pure.pure; exact PrefixPreserves.pure c.safe _)
    | (maintenance_head ForIn.forIn; apply PrefixPreserves.forIn _ _ _ c.safe; intro x b; change PrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

inductive ConfigurationCall where
  | port (port : Nat)
  | allowedIp (pid : PeerId) (attrs : AllowedIpAttrs)
  | peer (attrs : PeerAttrs)
  | device (attrs : DeviceAttrs)

namespace ConfigurationCall

def original : ConfigurationCall → WG.M Int
  | .port p => setPort p
  | .allowedIp pid attrs => setAllowedip pid attrs
  | .peer attrs => setPeerCmd attrs
  | .device attrs => wgSetDevice attrs

def observed : ConfigurationCall → MixedM Int
  | .port p => setPortPrefix p
  | .allowedIp pid attrs => setAllowedipPrefix pid attrs
  | .peer attrs => setPeerCmdPrefix attrs
  | .device attrs => wgSetDevicePrefix attrs

theorem erases (call : ConfigurationCall) : ErasesStatePrefix call.observed call.original := by
  cases call with
  | port port => exact setPortPrefix_erases port
  | allowedIp pid attrs => exact setAllowedipPrefix_erases pid attrs
  | peer attrs => exact setPeerCmdPrefix_erases attrs
  | device attrs => exact wgSetDevicePrefix_erases attrs

theorem preserves_ambient (c : AmbientContracts I) (hs : SocketControlStable I)
    (r : ConfigurationPeerContracts I) (d : ConfigurationDeviceContracts I) (call : ConfigurationCall) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe call.observed := by
  cases call with
  | port port => exact setPortPrefix_preserves c hs port
  | allowedIp pid attrs => exact setAllowedipPrefix_preserves c r.nodes pid attrs
  | peer attrs => exact setPeerCmdPrefix_preserves c r attrs
  | device attrs => exact wgSetDevicePrefix_preserves c hs r d attrs

theorem preserves_ambient_product (c : ProductAmbientContracts I) (hs : ProductSocketControlStable I)
    (r : ProductConfigurationPeerContracts I) (d : ProductConfigurationDeviceContracts I) (call : ConfigurationCall) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver call.observed) := by
  cases call with
  | port port => exact setPortPrefix_preserves_product c hs port
  | allowedIp pid attrs => exact setAllowedipPrefix_preserves_product c r.nodes pid attrs
  | peer attrs => exact setPeerCmdPrefix_preserves_product c r attrs
  | device attrs => exact wgSetDevicePrefix_preserves_product c hs r d attrs

theorem allocation (call : ConfigurationCall) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe call.observed :=
  call.preserves_ambient allocationAmbient allocationSocketControlStable allocationConfigurationPeer allocationConfigurationDevice

end ConfigurationCall
end Leanux.Proofs.WG.Lifetimes
