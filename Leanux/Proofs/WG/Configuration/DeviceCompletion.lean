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

def devicePeersObserved (a : DeviceAttrs) : PrefixM RoutingCompletion Int := do
  let zero (ret : Int) : PrefixM RoutingCompletion Int := do
    _ ← liftPrefix (branch .setDevZeroKey a.privateKey.isSome)
    return ret
  if ← liftPrefix (branch .setDevHasPeers a.peers.isSome) then
    for entry in a.peers.getD [] do
      _ ← liftPrefix (branch .setDevPeersIter true)
      match entry with
      | .malformed =>
        _ ← liftPrefix (branch .setDevParseErr true)
        return ← zero (-EINVAL)
      | .attrs p =>
        _ ← liftPrefix (branch .setDevParseErr false)
        let ret ← setPeerCmdObserved p
        if ← liftPrefix (branch .setDevSetPeerErr (ret < 0)) then return ← zero ret
    _ ← liftPrefix (branch .setDevPeersIter false)
  zero 0

def deviceKeyObserved (a : DeviceAttrs) : PrefixM RoutingCompletion Int := do
  if ← liftPrefix (WG.andM (branch .setDevHasPrivateKey a.privateKey.isSome) (branch .setDevPrivateKeyLen true)) then
    let some key := a.privateKey | liftPrefix (invariant "unreachable")
    if !(← liftPrefix (branch .setDevKeyUnchanged ((← liftPrefix getDev).staticIdentity.staticPrivate == key))) then
      let (pub, ok) ← liftPrefix (generatePublic key)
      if ← liftPrefix (branch .setDevGenPublic ok) then
        let some pub := pub | liftPrefix (invariant "a generated public key without a write")
        let peer ← liftPrefix (pubkeyLookup pub)
        if ← liftPrefix (branch .setDevOldPeer peer.isSome) then
          liftPrefix (peerPut peer)
          peerRemoveObserved peer
      let d ← liftPrefix getDev
      let sendStaged ← liftPrefix (WG.andM (branch .setDevSendStagedNoIdentity !d.staticIdentity.hasIdentity)
        (branch .setDevSendStagedRunning d.running))
      liftPrefix (setStaticIdentityPrivateKey key)
      let hasIdentity := (← liftPrefix getDev).staticIdentity.hasIdentity
      let sendStaged ← liftPrefix (WG.andM (branch .setDevSendStagedKept sendStaged) (branch .setDevSendStagedHasIdentity hasIdentity))
      liftPrefix cookiePrecomputeDeviceKeys
      for pid in (← liftPrefix getDev).peerList do
        _ ← liftPrefix (branch .setDevKeyPeerIter true)
        liftPrefix (precomputeStaticStatic pid)
        liftPrefix (expireCurrentPeerKeypairs pid)
        if ← liftPrefix (branch .setDevSendStagedPeer sendStaged) then liftPrefix (sendStagedPackets pid)
      _ ← liftPrefix (branch .setDevKeyPeerIter false)
  devicePeersObserved a

def deviceUpdateObserved (a : DeviceAttrs) (flags : UInt32) : PrefixM RoutingCompletion Int := do
  let zero (ret : Int) : PrefixM RoutingCompletion Int := do
    _ ← liftPrefix (branch .setDevZeroKey a.privateKey.isSome)
    return ret
  liftPrefix (modifyDev fun d => {d with deviceUpdateGen := d.deviceUpdateGen + 1})
  if ← liftPrefix (branch .setDevFwmark a.fwmark.isSome) then
    liftPrefix (modifyDev fun d => {d with fwmark := a.fwmark.getD 0})
    for pid in (← liftPrefix getDev).peerList do
      _ ← liftPrefix (branch .setDevFwmarkPeerIter true)
      liftPrefix (clearPeerEndpointSrc pid)
    _ ← liftPrefix (branch .setDevFwmarkPeerIter false)
  if ← liftPrefix (branch .setDevPort a.listenPort.isSome) then
    let ret ← liftPrefix (setPort (a.listenPort.getD 0))
    if ← liftPrefix (branch .setDevPortErr (ret != 0)) then return ← zero ret
  if ← liftPrefix (branch .setDevReplacePeers (flags &&& WGDEVICE_F_REPLACE_PEERS != 0)) then peerRemoveAllObserved
  deviceKeyObserved a

def wgSetDeviceObserved (a : DeviceAttrs) : PrefixM RoutingCompletion Int := do
  let zero (ret : Int) : PrefixM RoutingCompletion Int := do
    _ ← liftPrefix (branch .setDevZeroKey a.privateKey.isSome)
    return ret
  let wg ← liftPrefix (lookupInterface a.device)
  if ← liftPrefix (branch .setDevLookupErr (wg matches .error _)) then
    let .error e := wg | liftPrefix (invariant "unreachable")
    return ← zero e
  let mut flags : UInt32 := 0
  if ← liftPrefix (branch .setDevHasFlags a.flags.isSome) then flags := a.flags.getD 0
  if ← liftPrefix (branch .setDevBadFlags (flags &&& ~~~WGDEVICE_F_ALL != 0)) then return ← zero (-EOPNOTSUPP)
  if ← liftPrefix (WG.orM (branch .setDevHasPort a.listenPort.isSome) (branch .setDevHasFwmark a.fwmark.isSome)) then
    let denied ← liftPrefix (WG.orM (branch .setDevNoNet !(← liftPrefix getDev).creatingNet) (branch .setDevNotCapable false))
    if ← liftPrefix (branch .setDevPermErr denied) then return ← zero (-EPERM)
  deviceUpdateObserved a flags

theorem devicePeersObserved_erases (a : DeviceAttrs) :
    ErasesPrefix (devicePeersObserved a) (devicePeersSource a) := by
  unfold devicePeersObserved devicePeersSource
  simp only [bind_assoc, pure_bind]
  repeat' first
    | with_reducible exact setPeerCmdObserved_erases _
    | with_reducible exact peerRemoveObserved_erases _
    | with_reducible exact peerRemoveAllObserved_erases
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals simp_all
  all_goals first | exact erasesPrefix_lift _ | exact erasesPrefix_pure _

theorem deviceKeyObserved_erases (a : DeviceAttrs) :
    ErasesPrefix (deviceKeyObserved a) (deviceKeySource a) := by
  unfold deviceKeyObserved deviceKeySource
  simp only [bind_assoc, pure_bind]
  repeat' first
    | with_reducible exact devicePeersObserved_erases _
    | with_reducible exact setPeerCmdObserved_erases _
    | with_reducible exact peerRemoveObserved_erases _
    | with_reducible exact peerRemoveAllObserved_erases
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals simp_all
  all_goals first | exact erasesPrefix_lift _ | exact erasesPrefix_pure _

theorem deviceUpdateObserved_erases (a : DeviceAttrs) (flags : UInt32) :
    ErasesPrefix (deviceUpdateObserved a flags) (deviceUpdateSource a flags) := by
  unfold deviceUpdateObserved deviceUpdateSource
  simp only [bind_assoc, pure_bind]
  repeat' first
    | with_reducible exact devicePeersObserved_erases _
    | with_reducible exact deviceKeyObserved_erases _
    | with_reducible exact setPeerCmdObserved_erases _
    | with_reducible exact peerRemoveObserved_erases _
    | with_reducible exact peerRemoveAllObserved_erases
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals simp_all
  all_goals first | exact erasesPrefix_lift _ | exact erasesPrefix_pure _

theorem wgSetDeviceObserved_erases (a : DeviceAttrs) :
    ErasesPrefix (wgSetDeviceObserved a) (wgSetDevice a) := by
  rw [← wgSetDevice_source]
  unfold wgSetDeviceObserved wgSetDeviceSource
  simp only [bind_assoc, pure_bind]
  repeat' first
    | with_reducible exact devicePeersObserved_erases _
    | with_reducible exact deviceKeyObserved_erases _
    | with_reducible exact deviceUpdateObserved_erases _ _
    | with_reducible exact setPeerCmdObserved_erases _
    | with_reducible exact peerRemoveObserved_erases _
    | with_reducible exact peerRemoveAllObserved_erases
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals simp_all
  all_goals first | exact erasesPrefix_lift _ | exact erasesPrefix_pure _


private theorem completion_state_safe (initial : FlatTable × FlatTable) :
    ∀ h w, CompletionState initial h w → CompletionSafe initial h := fun _ _ hi => hi.1

private theorem device_lift_same (initial : FlatTable × FlatTable) (a : M α)
    (ha : SameView routingView a) :
    PrefixPreserves (CompletionState initial) (CompletionSafe initial) (liftPrefix a) :=
  completion_lift_retains initial a (.of_same ha)

private theorem device_lift_kernel (initial : FlatTable × FlatTable) (a : M α)
    (ha : SameKernel a) :
    PrefixPreserves (CompletionState initial) (CompletionSafe initial) (liftPrefix a) :=
  device_lift_same initial a (routing_kernel a ha)

private theorem device_bad (initial : FlatTable × FlatTable) (message : String) :
    PrefixPreserves (CompletionState initial) (CompletionSafe initial)
      (liftPrefix (invariant message : M α)) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift _ (completion_state_safe initial)
  intro h w x v hi hr
  cases hr

private theorem device_lookup (initial : FlatTable × FlatTable) (key : Key) :
    PrefixPreserves (CompletionState initial) (CompletionSafe initial) (liftPrefix (pubkeyLookup key)) :=
  ((pubkeyLookup_completion initial key).consequence (fun _ _ h => h) (fun _ _ _ h => h.1)).preserves

/-- Membership is required only for the actual captured attribute list; arbitrary
malformed entries still execute their original ordinary-error path. -/
private theorem forIn_device_members (initial : FlatTable × FlatTable) (xs : List α) (b : β)
    (g : α → β → PrefixM RoutingCompletion (ForInStep β))
    (hg : ∀ x ∈ xs, ∀ b, PrefixPreserves (CompletionState initial) (CompletionSafe initial) (g x b)) :
    PrefixPreserves (CompletionState initial) (CompletionSafe initial) (forIn xs b g) := by
  induction xs generalizing b with
  | nil => simpa only [List.forIn_nil] using PrefixPreserves.pure (completion_state_safe initial) b
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply PrefixPreserves.bind (hg x (by simp) b)
    intro step
    cases step with
    | done b => exact PrefixPreserves.pure (completion_state_safe initial) b
    | yield b => exact ih b (fun y hy b => hg y (by simp [hy]) b)

theorem devicePeersObserved_spec (initial : FlatTable × FlatTable) (a : DeviceAttrs)
    (shape : DeviceAddressShape a) :
    PrefixEnsures (CompletionState initial) (CompletionSafe initial)
      (devicePeersObserved a) (fun _ => CompletionState initial) := by
  change PrefixPreserves (CompletionState initial) (CompletionSafe initial) _
  have hb := fun d b => device_lift_kernel initial _ (sameKernel_branch d b)
  unfold devicePeersObserved
  apply PrefixPreserves.bind (hb _ _)
  intro has
  split
  · dsimp only
    refine PrefixPreserves.bind (forIn_device_members initial _ _ _ ?_) ?_
    · intro entry he acc
      try dsimp only
      apply PrefixPreserves.bind (hb _ _)
      intro _
      cases entry with
      | malformed =>
        repeat' first
          | with_reducible exact hb _ _
          | with_reducible exact PrefixPreserves.pure (completion_state_safe initial) _
          | with_reducible apply PrefixPreserves.bind
          | (with_reducible intro x; try dsimp only)
      | attrs p =>
        have hp := (setPeerCmdObserved_spec initial p (shape p he)).preserves
        repeat' first
          | with_reducible exact hp
          | with_reducible exact hb _ _
          | with_reducible exact PrefixPreserves.pure (completion_state_safe initial) _
          | with_reducible apply PrefixPreserves.bind
          | (with_reducible intro x; try dsimp only)
          | (with_reducible split)
    · intro result
      rcases result with ⟨early, acc⟩
      cases early <;> dsimp only
      all_goals
        repeat' first
          | with_reducible exact hb _ _
          | with_reducible exact PrefixPreserves.pure (completion_state_safe initial) _
          | with_reducible apply PrefixPreserves.bind
          | (with_reducible intro x; try dsimp only)
  · exact PrefixPreserves.bind (hb _ _) (fun _ => PrefixPreserves.pure (completion_state_safe initial) _)

theorem deviceKeyObserved_spec (initial : FlatTable × FlatTable) (a : DeviceAttrs)
    (shape : DeviceAddressShape a) :
    PrefixEnsures (CompletionState initial) (CompletionSafe initial)
      (deviceKeyObserved a) (fun _ => CompletionState initial) := by
  change PrefixPreserves (CompletionState initial) (CompletionSafe initial) _
  have peers := (devicePeersObserved_spec initial a shape).preserves
  have remove := fun peer => (peerRemoveObserved_spec initial peer).preserves
  unfold deviceKeyObserved
  repeat' first
    | with_reducible exact peers
    | with_reducible exact remove _
    | with_reducible exact device_lookup initial _
    | with_reducible exact completion_lift_retains initial _ (peerPut_retainsRouting _)
    | with_reducible exact completion_lift_retains initial _ (sendStagedPackets_routing _)
    | with_reducible exact device_lift_same initial _ (precomputeStaticStatic_routing _)
    | with_reducible exact device_lift_same initial _ (expireCurrentPeerKeypairs_routing _)
    | with_reducible exact device_lift_same initial _ (configuration_routing _ (setStaticIdentityPrivateKey_sameConfiguration _))
    | with_reducible exact device_lift_same initial _ (configuration_routing _ cookiePrecomputeDeviceKeys_sameConfiguration)
    | with_reducible exact device_bad initial _
    | (solve | with_reducible apply device_lift_kernel initial; repeat' first | exact sameKernel_branch _ _ | exact getDev_sameKernel | exact generatePublic_sameKernel _ | apply andM_sameKernel)
    | with_reducible exact PrefixPreserves.pure (completion_state_safe initial) _
    | with_reducible apply PrefixPreserves.forIn _ _ _ (completion_state_safe initial)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem deviceUpdateObserved_spec (initial : FlatTable × FlatTable) (a : DeviceAttrs)
    (flags : UInt32) (shape : DeviceAddressShape a) :
    PrefixEnsures (CompletionState initial) (CompletionSafe initial)
      (deviceUpdateObserved a flags) (fun _ => CompletionState initial) := by
  change PrefixPreserves (CompletionState initial) (CompletionSafe initial) _
  have key := (deviceKeyObserved_spec initial a shape).preserves
  have remove := (peerRemoveAllObserved_spec initial).preserves
  unfold deviceUpdateObserved
  repeat' first
    | with_reducible exact key
    | with_reducible exact remove
    | with_reducible exact device_lift_same initial _ (modifyDev_routing (fun d => {d with deviceUpdateGen := d.deviceUpdateGen + 1}) (fun _ => rfl))
    | with_reducible exact device_lift_same initial _ (modifyDev_routing (fun d => {d with fwmark := a.fwmark.getD 0}) (fun _ => rfl))
    | with_reducible exact device_lift_same initial _ (clearPeerEndpointSrc_routing _)
    | with_reducible exact device_lift_same initial _ (setPort_routing _)
    | with_reducible exact device_bad initial _
    | (solve | with_reducible apply device_lift_kernel initial; repeat' first | exact sameKernel_branch _ _ | exact getDev_sameKernel)
    | with_reducible exact PrefixPreserves.pure (completion_state_safe initial) _
    | with_reducible apply PrefixPreserves.forIn _ _ _ (completion_state_safe initial)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem wgSetDeviceObserved_spec (initial : FlatTable × FlatTable) (a : DeviceAttrs)
    (shape : DeviceAddressShape a) :
    PrefixEnsures (CompletionState initial) (CompletionSafe initial)
      (wgSetDeviceObserved a) (fun _ => CompletionState initial) := by
  change PrefixPreserves (CompletionState initial) (CompletionSafe initial) _
  have update := fun flags => (deviceUpdateObserved_spec initial a flags shape).preserves
  unfold wgSetDeviceObserved
  repeat' first
    | with_reducible exact update _
    | with_reducible exact device_bad initial _
    | (solve | with_reducible apply device_lift_kernel initial; repeat' first | exact sameKernel_branch _ _ | exact getDev_sameKernel | exact lookupInterface_sameKernel _ | apply orM_sameKernel)
    | with_reducible exact PrefixPreserves.pure (completion_state_safe initial) _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

end Leanux.Proofs.WG.Configuration
