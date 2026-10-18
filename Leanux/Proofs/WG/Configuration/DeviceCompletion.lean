import Leanux.Proofs.WG.Configuration.PeerCommandCompletion
import Leanux.Proofs.WG.Configuration.ParserShape
import Leanux.Proofs.WG.Configuration.DeviceSource
import Leanux.Proofs.WG.AllowedIps.RoutingDeviceFrames

/-! Original device configuration with completed routing cuts. Guards and
nonrouting helpers run unchanged; every completed nested routing operation is
retained if later cleanup Stops. Device presence is an entry invariant, not an
assumption on arbitrary-input erasure. -/
namespace Leanux.Proofs.WG.Configuration
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Leanux.Proofs.WG.AllowedIps Leanux.Proofs.WG.Lifetimes
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

def devicePeersObserved (a : DeviceAttrs) : WGPrefix RoutingCompletion Int := do
  let zero (ret : Int) : WGPrefix RoutingCompletion Int := do
    _ ← liftWGPrefix (branch .setDevZeroKey a.privateKey.isSome)
    return ret
  if ← liftWGPrefix (branch .setDevHasPeers a.peers.isSome) then
    for entry in a.peers.getD [] do
      _ ← liftWGPrefix (branch .setDevPeersIter true)
      match entry with
      | .malformed =>
        _ ← liftWGPrefix (branch .setDevParseErr true)
        return ← zero (-EINVAL)
      | .attrs p =>
        _ ← liftWGPrefix (branch .setDevParseErr false)
        let ret ← setPeerCmdObserved p
        if ← liftWGPrefix (branch .setDevSetPeerErr (ret < 0)) then return ← zero ret
    _ ← liftWGPrefix (branch .setDevPeersIter false)
  zero 0

def deviceKeyObserved (a : DeviceAttrs) : WGPrefix RoutingCompletion Int := do
  if ← liftWGPrefix (WG.andM (branch .setDevHasPrivateKey a.privateKey.isSome) (branch .setDevPrivateKeyLen true)) then
    let some key := a.privateKey | liftWGPrefix (invariant "unreachable")
    if !(← liftWGPrefix (branch .setDevKeyUnchanged ((← liftWGPrefix getDev).staticIdentity.staticPrivate == key))) then
      let (pub, ok) ← liftWGPrefix (generatePublic key)
      if ← liftWGPrefix (branch .setDevGenPublic ok) then
        let some pub := pub | liftWGPrefix (invariant "a generated public key without a write")
        let peer ← liftWGPrefix (pubkeyLookup pub)
        if ← liftWGPrefix (branch .setDevOldPeer peer.isSome) then
          liftWGPrefix (peerPut peer)
          peerRemoveObserved peer
      let d ← liftWGPrefix getDev
      let sendStaged ← liftWGPrefix (WG.andM (branch .setDevSendStagedNoIdentity !d.staticIdentity.hasIdentity)
        (branch .setDevSendStagedRunning d.running))
      liftWGPrefix (setStaticIdentityPrivateKey key)
      let hasIdentity := (← liftWGPrefix getDev).staticIdentity.hasIdentity
      let sendStaged ← liftWGPrefix (WG.andM (branch .setDevSendStagedKept sendStaged) (branch .setDevSendStagedHasIdentity hasIdentity))
      liftWGPrefix cookiePrecomputeDeviceKeys
      for pid in (← liftWGPrefix getDev).peerList do
        _ ← liftWGPrefix (branch .setDevKeyPeerIter true)
        liftWGPrefix (precomputeStaticStatic pid)
        liftWGPrefix (expireCurrentPeerKeypairs pid)
        if ← liftWGPrefix (branch .setDevSendStagedPeer sendStaged) then liftWGPrefix (sendStagedPackets pid)
      _ ← liftWGPrefix (branch .setDevKeyPeerIter false)
  devicePeersObserved a

def deviceUpdateObserved (a : DeviceAttrs) (flags : UInt32) : WGPrefix RoutingCompletion Int := do
  let zero (ret : Int) : WGPrefix RoutingCompletion Int := do
    _ ← liftWGPrefix (branch .setDevZeroKey a.privateKey.isSome)
    return ret
  liftWGPrefix (modifyDev fun d => {d with deviceUpdateGen := d.deviceUpdateGen + 1})
  if ← liftWGPrefix (branch .setDevFwmark a.fwmark.isSome) then
    liftWGPrefix (modifyDev fun d => {d with fwmark := a.fwmark.getD 0})
    for pid in (← liftWGPrefix getDev).peerList do
      _ ← liftWGPrefix (branch .setDevFwmarkPeerIter true)
      liftWGPrefix (clearPeerEndpointSrc pid)
    _ ← liftWGPrefix (branch .setDevFwmarkPeerIter false)
  if ← liftWGPrefix (branch .setDevPort a.listenPort.isSome) then
    let ret ← liftWGPrefix (setPort (a.listenPort.getD 0))
    if ← liftWGPrefix (branch .setDevPortErr (ret != 0)) then return ← zero ret
  if ← liftWGPrefix (branch .setDevReplacePeers (flags &&& WGDEVICE_F_REPLACE_PEERS != 0)) then peerRemoveAllObserved
  deviceKeyObserved a

def wgSetDeviceObserved (a : DeviceAttrs) : WGPrefix RoutingCompletion Int := do
  let zero (ret : Int) : WGPrefix RoutingCompletion Int := do
    _ ← liftWGPrefix (branch .setDevZeroKey a.privateKey.isSome)
    return ret
  let wg ← liftWGPrefix (lookupInterface a.device)
  if ← liftWGPrefix (branch .setDevLookupErr (wg matches .error _)) then
    let .error e := wg | liftWGPrefix (invariant "unreachable")
    return ← zero e
  let mut flags : UInt32 := 0
  if ← liftWGPrefix (branch .setDevHasFlags a.flags.isSome) then flags := a.flags.getD 0
  if ← liftWGPrefix (branch .setDevBadFlags (flags &&& ~~~WGDEVICE_F_ALL != 0)) then return ← zero (-EOPNOTSUPP)
  if ← liftWGPrefix (WG.orM (branch .setDevHasPort a.listenPort.isSome) (branch .setDevHasFwmark a.fwmark.isSome)) then
    let denied ← liftWGPrefix (WG.orM (branch .setDevNoNet !(← liftWGPrefix getDev).creatingNet) (branch .setDevNotCapable false))
    if ← liftWGPrefix (branch .setDevPermErr denied) then return ← zero (-EPERM)
  deviceUpdateObserved a flags

theorem devicePeersObserved_erases (a : DeviceAttrs) :
    ErasesStatePrefix (devicePeersObserved a) (devicePeersSource a) := by
  unfold devicePeersObserved devicePeersSource
  repeat' first
    | contradiction
    | maintenance_impossible_match
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_erases_bind
    | (maintenance_head setPeerCmdObserved; exact setPeerCmdObserved_erases _)
    | (maintenance_head peerRemoveObserved; exact peerRemoveObserved_erases _)
    | (maintenance_head peerRemoveAllObserved; exact peerRemoveAllObserved_erases)
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | (maintenance_head ForIn.forIn; apply erasesStatePrefix_forIn)
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro
    | rfl

theorem deviceKeyObserved_erases (a : DeviceAttrs) :
    ErasesStatePrefix (deviceKeyObserved a) (deviceKeySource a) := by
  unfold deviceKeyObserved deviceKeySource
  repeat' first
    | contradiction
    | maintenance_impossible_match
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_erases_bind
    | (maintenance_head devicePeersObserved; exact devicePeersObserved_erases _)
    | (maintenance_head setPeerCmdObserved; exact setPeerCmdObserved_erases _)
    | (maintenance_head peerRemoveObserved; exact peerRemoveObserved_erases _)
    | (maintenance_head peerRemoveAllObserved; exact peerRemoveAllObserved_erases)
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | (maintenance_head ForIn.forIn; apply erasesStatePrefix_forIn)
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro
    | rfl

theorem deviceUpdateObserved_erases (a : DeviceAttrs) (flags : UInt32) :
    ErasesStatePrefix (deviceUpdateObserved a flags) (deviceUpdateSource a flags) := by
  unfold deviceUpdateObserved deviceUpdateSource
  repeat' first
    | contradiction
    | maintenance_impossible_match
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_erases_bind
    | (maintenance_head devicePeersObserved; exact devicePeersObserved_erases _)
    | (maintenance_head deviceKeyObserved; exact deviceKeyObserved_erases _)
    | (maintenance_head setPeerCmdObserved; exact setPeerCmdObserved_erases _)
    | (maintenance_head peerRemoveObserved; exact peerRemoveObserved_erases _)
    | (maintenance_head peerRemoveAllObserved; exact peerRemoveAllObserved_erases)
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | (maintenance_head ForIn.forIn; apply erasesStatePrefix_forIn)
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro
    | rfl

theorem wgSetDeviceObserved_erases (a : DeviceAttrs) :
    ErasesStatePrefix (wgSetDeviceObserved a) (wgSetDevice a) := by
  rw [← wgSetDevice_source]
  unfold wgSetDeviceObserved wgSetDeviceSource
  repeat' first
    | contradiction
    | maintenance_impossible_match
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_erases_bind
    | (maintenance_head devicePeersObserved; exact devicePeersObserved_erases _)
    | (maintenance_head deviceKeyObserved; exact deviceKeyObserved_erases _)
    | (maintenance_head deviceUpdateObserved; exact deviceUpdateObserved_erases _ _)
    | (maintenance_head setPeerCmdObserved; exact setPeerCmdObserved_erases _)
    | (maintenance_head peerRemoveObserved; exact peerRemoveObserved_erases _)
    | (maintenance_head peerRemoveAllObserved; exact peerRemoveAllObserved_erases)
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | (maintenance_head ForIn.forIn; apply erasesStatePrefix_forIn)
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro
    | rfl


private theorem completion_state_safe (initial : FlatTable × FlatTable) :
    ∀ h w, CompletionState initial h w → CompletionSafe initial h := fun _ _ hi => hi.1

private theorem device_lift_same_wg (initial : FlatTable × FlatTable) (a : WG.M α)
    (ha : SameView routingView a) :
    StatePrefixPreserves (fun h w _ => CompletionState initial h w) (CompletionSafe initial) (liftWGPrefix a) :=
  completion_lift_retains_wg initial a (ProjectedRetainsRoutingCall.of_same ha)

private theorem device_lift_kernel_wg (initial : FlatTable × FlatTable) (a : WG.M α)
    (ha : SameWGStore a) :
    StatePrefixPreserves (fun h w _ => CompletionState initial h w) (CompletionSafe initial) (liftWGPrefix a) :=
  device_lift_same_wg initial a (routing_kernel (project := id) a ha)

private theorem device_bad_wg (initial : FlatTable × FlatTable) (message : String) :
    StatePrefixPreserves (fun h w _ => CompletionState initial h w) (CompletionSafe initial)
      (liftWGPrefix (invariant message : WG.M α)) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1)
  intro h w ambient x v ambient' hi hr
  cases hr

private theorem device_lookup (initial : FlatTable × FlatTable) (key : Key) :
    StatePrefixPreserves (fun h w _ => CompletionState initial h w) (CompletionSafe initial)
      (liftWGPrefix (pubkeyLookup key)) :=
  (pubkeyLookup_completion initial key).consequence (fun _ _ _ h => h) (fun _ _ _ _ h => h.1)

/-- Membership concerns the actual captured attribute list, including malformed entries. -/
private theorem forIn_device_members_wg (initial : FlatTable × FlatTable) (xs : List α) (b : β)
    (g : α → β → WGPrefix RoutingCompletion (ForInStep β))
    (hg : ∀ x ∈ xs, ∀ b, StatePrefixPreserves (fun h w _ => CompletionState initial h w)
      (CompletionSafe initial) (g x b)) :
    StatePrefixPreserves (fun h w _ => CompletionState initial h w)
      (CompletionSafe initial) (forIn xs b g) := by
  induction xs generalizing b with
  | nil => exact StatePrefixEnsures.pure b (fun _ _ _ hi => hi.1) (fun _ _ _ hi => hi)
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply StatePrefixEnsures.bind (hg x (by simp) b)
    intro step
    cases step with
    | done b => exact StatePrefixEnsures.pure b (fun _ _ _ hi => hi.1) (fun _ _ _ hi => hi)
    | yield b => exact ih b (fun y hy b => hg y (by simp [hy]) b)

theorem devicePeersObserved_spec (initial : FlatTable × FlatTable) (a : DeviceAttrs)
    (shape : DeviceAddressShape a) :
    StatePrefixEnsures (fun h w _ => CompletionState initial h w) (CompletionSafe initial)
      (devicePeersObserved a) (fun _ h w _ => CompletionState initial h w) := by
  have hb (d : Decision) (b : Bool) :
      StatePrefixPreserves (fun h w _ => CompletionState initial h w) (CompletionSafe initial)
        (liftWGPrefix (branch d b)) :=
    device_lift_kernel_wg initial _ (fun saved =>
      hoare_liftAmbient (AmbientM.branch d b) (fun g => wgStoreView g = saved))
  unfold devicePeersObserved
  apply StatePrefixEnsures.bind (hb _ _)
  intro has
  split
  · dsimp only
    refine StatePrefixEnsures.bind (forIn_device_members_wg initial _ _ _ ?_) ?_
    · intro entry he acc
      try dsimp only
      apply StatePrefixEnsures.bind (hb _ _)
      intro _
      cases entry with
      | malformed =>
        repeat' first
          | contradiction
          | unfold StatePrefixPreserves
          | maintenance_join_let
          | maintenance_join_use
          | maintenance_reduce
          | maintenance_reduce_match
          | with_reducible exact hb _ _
          | exact StatePrefixEnsures.pure _ (fun h w _ hi => completion_state_safe initial h w hi) (fun _ _ _ hi => hi)
          | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => CompletionState initial h w))
          | (maintenance_intro; try dsimp only)
      | attrs p =>
        have hp := (setPeerCmdObserved_spec initial p (shape p he))
        repeat' first
          | contradiction
          | unfold StatePrefixPreserves
          | maintenance_join_let
          | maintenance_join_use
          | maintenance_reduce
          | maintenance_reduce_match
          | with_reducible exact hp
          | with_reducible exact hb _ _
          | exact StatePrefixEnsures.pure _ (fun h w _ hi => completion_state_safe initial h w hi) (fun _ _ _ hi => hi)
          | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => CompletionState initial h w))
          | (maintenance_intro; try dsimp only)
          | (with_reducible split)
    · intro result
      rcases result with ⟨early, acc⟩
      cases early <;> dsimp only
      all_goals
        repeat' first
          | contradiction
          | unfold StatePrefixPreserves
          | maintenance_join_let
          | maintenance_join_use
          | maintenance_reduce
          | maintenance_reduce_match
          | with_reducible exact hb _ _
          | exact StatePrefixEnsures.pure _ (fun h w _ hi => completion_state_safe initial h w hi) (fun _ _ _ hi => hi)
          | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => CompletionState initial h w))
          | (maintenance_intro; try dsimp only)
  · exact StatePrefixEnsures.bind (hb _ _) (fun _ => StatePrefixEnsures.pure _ (fun h w _ hi => completion_state_safe initial h w hi) (fun _ _ _ hi => hi))

theorem deviceKeyObserved_spec (initial : FlatTable × FlatTable) (a : DeviceAttrs)
    (shape : DeviceAddressShape a) :
    StatePrefixEnsures (fun h w _ => CompletionState initial h w) (CompletionSafe initial)
      (deviceKeyObserved a) (fun _ h w _ => CompletionState initial h w) := by
  have peers := (devicePeersObserved_spec initial a shape)
  have remove := fun peer => (peerRemoveObserved_spec initial peer)
  have hb (d : Decision) (b : Bool) : SameWGStore (branch d b) :=
    fun saved => hoare_liftAmbient (AmbientM.branch d b) (fun g => wgStoreView g = saved)
  unfold deviceKeyObserved
  repeat' first
    | contradiction
    | unfold StatePrefixPreserves
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | with_reducible exact peers
    | with_reducible exact remove _
    | with_reducible exact device_lookup initial _
    | with_reducible exact completion_lift_retains_wg initial _ (peerPut_retainsRouting _)
    | with_reducible exact completion_lift_retains_wg initial _ (sendStagedPackets_routing _)
    | with_reducible exact device_lift_same_wg initial _ (precomputeStaticStatic_routing _)
    | with_reducible exact device_lift_same_wg initial _ (expireCurrentPeerKeypairs_routing _)
    | with_reducible exact device_lift_same_wg initial _ (configuration_routing_native _ (setStaticIdentityPrivateKey_sameConfiguration _))
    | with_reducible exact device_lift_same_wg initial _ (configuration_routing_native _ cookiePrecomputeDeviceKeys_sameConfiguration)
    | with_reducible exact device_bad_wg initial _
    | (maintenance_lift_action_head branch; exact device_lift_kernel_wg initial _ (hb _ _))
    | (maintenance_lift_action_head getDev; exact device_lift_kernel_wg initial _ getDev_sameWGStore)
    | (maintenance_lift_action_head generatePublic; exact device_lift_kernel_wg initial _ ((generatePublic_sameWGWorld _).factor wgStoreView))
    | (maintenance_lift_action_head WG.andM; exact device_lift_kernel_wg initial _ (DumpComposition.andM_sameView _ _ (hb _ _) (hb _ _)))
    | exact StatePrefixEnsures.pure _ (fun h w _ hi => completion_state_safe initial h w hi) (fun _ _ _ hi => hi)
    | (maintenance_head ForIn.forIn; apply forIn_device_members_wg; intro _ _ _)
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => CompletionState initial h w))
    | (maintenance_intro; try dsimp only)
    | (with_reducible split)

theorem deviceUpdateObserved_spec (initial : FlatTable × FlatTable) (a : DeviceAttrs)
    (flags : UInt32) (shape : DeviceAddressShape a) :
    StatePrefixEnsures (fun h w _ => CompletionState initial h w) (CompletionSafe initial)
      (deviceUpdateObserved a flags) (fun _ h w _ => CompletionState initial h w) := by
  have key := (deviceKeyObserved_spec initial a shape)
  have remove := (peerRemoveAllObserved_spec initial)
  have hb (d : Decision) (b : Bool) : SameWGStore (branch d b) :=
    fun saved => hoare_liftAmbient (AmbientM.branch d b) (fun g => wgStoreView g = saved)
  unfold deviceUpdateObserved
  repeat' first
    | contradiction
    | unfold StatePrefixPreserves
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | with_reducible exact key
    | with_reducible exact remove
    | with_reducible exact device_lift_same_wg initial _ (modifyDev_routing (fun d => {d with deviceUpdateGen := d.deviceUpdateGen + 1}) (fun _ => rfl))
    | with_reducible exact device_lift_same_wg initial _ (modifyDev_routing (fun d => {d with fwmark := a.fwmark.getD 0}) (fun _ => rfl))
    | with_reducible exact device_lift_same_wg initial _ (clearPeerEndpointSrc_routing _)
    | with_reducible exact device_lift_same_wg initial _ (setPort_routing _)
    | with_reducible exact device_bad_wg initial _
    | (maintenance_lift_action_head branch; exact device_lift_kernel_wg initial _ (hb _ _))
    | (maintenance_lift_action_head getDev; exact device_lift_kernel_wg initial _ getDev_sameWGStore)
    | exact StatePrefixEnsures.pure _ (fun h w _ hi => completion_state_safe initial h w hi) (fun _ _ _ hi => hi)
    | (maintenance_head ForIn.forIn; apply forIn_device_members_wg; intro _ _ _)
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => CompletionState initial h w))
    | (maintenance_intro; try dsimp only)
    | (with_reducible split)

theorem wgSetDeviceObserved_spec (initial : FlatTable × FlatTable) (a : DeviceAttrs)
    (shape : DeviceAddressShape a) :
    StatePrefixEnsures (fun h w _ => CompletionState initial h w) (CompletionSafe initial)
      (wgSetDeviceObserved a) (fun _ h w _ => CompletionState initial h w) := by
  have update := fun flags => (deviceUpdateObserved_spec initial a flags shape)
  have hb (d : Decision) (b : Bool) : SameWGStore (branch d b) :=
    fun saved => hoare_liftAmbient (AmbientM.branch d b) (fun g => wgStoreView g = saved)
  unfold wgSetDeviceObserved
  repeat' first
    | contradiction
    | unfold StatePrefixPreserves
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | with_reducible exact update _
    | with_reducible exact device_bad_wg initial _
    | (maintenance_lift_action_head branch; exact device_lift_kernel_wg initial _ (hb _ _))
    | (maintenance_lift_action_head getDev; exact device_lift_kernel_wg initial _ getDev_sameWGStore)
    | (maintenance_lift_action_head lookupInterface; exact device_lift_kernel_wg initial _ ((lookupInterface_sameWGWorld _).factor wgStoreView))
    | (maintenance_lift_action_head WG.orM; exact device_lift_kernel_wg initial _ (DumpComposition.orM_sameView _ _ (hb _ _) (hb _ _)))
    | exact StatePrefixEnsures.pure _ (fun h w _ hi => completion_state_safe initial h w hi) (fun _ _ _ hi => hi)
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => CompletionState initial h w))
    | (maintenance_intro; try dsimp only)
    | (with_reducible split)


private theorem device_lift_same (initial : FlatTable × FlatTable) (a : Leanux.M α)
    (ha : SameView (fun w : World => routingView w.wg) a) :
    PrefixPreserves (fun h (w : World) => CompletionState initial h w.wg)
      (CompletionSafe initial) (liftPrefix a) :=
  completion_lift_retains World.wg initial a (ProjectedRetainsRoutingCall.of_same ha)

private theorem device_lift_kernel (initial : FlatTable × FlatTable) (a : Leanux.M α)
    (ha : SameProductStore a) :
    PrefixPreserves (fun h (w : World) => CompletionState initial h w.wg)
      (CompletionSafe initial) (liftPrefix a) :=
  device_lift_same initial a (routing_kernel a (ha.of_factor
    (fun s : ProductStore43 => s.2.2.2) (fun w : World => wgStoreView w.wg) (fun _ => rfl)))

private theorem device_bad (initial : FlatTable × FlatTable) (message : String) :
    PrefixPreserves (fun h (w : World) => CompletionState initial h w.wg) (CompletionSafe initial)
      (liftPrefix (invariant message : Leanux.M α)) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.1)
  intro h w x v hi hr
  cases hr

private theorem forIn_device_members (initial : FlatTable × FlatTable) (xs : List α) (b : β)
    (g : α → β → PrefixM RoutingCompletion (ForInStep β))
    (hg : ∀ x ∈ xs, ∀ b, PrefixPreserves (fun h (w : World) => CompletionState initial h w.wg)
      (CompletionSafe initial) (g x b)) :
    PrefixPreserves (fun h (w : World) => CompletionState initial h w.wg)
      (CompletionSafe initial) (forIn xs b g) := by
  induction xs generalizing b with
  | nil => simpa only [List.forIn_nil] using PrefixPreserves.pure (fun _ _ hi => hi.1) b
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply PrefixPreserves.bind (hg x (by simp) b)
    intro step
    cases step with
    | done b => exact PrefixPreserves.pure (fun _ _ hi => hi.1) b
    | yield b => exact ih b (fun y hy b => hg y (by simp [hy]) b)

end Leanux.Proofs.WG.Configuration
