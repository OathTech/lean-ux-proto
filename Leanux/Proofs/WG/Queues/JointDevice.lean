import Leanux.Proofs.WG.Queues.JointPeerCommand
import Leanux.Proofs.WG.Configuration.DeviceCompletion
import Leanux.Proofs.WG.Lifetimes.ConfigurationDevice

/-! Joint device configuration uses the exact existing source continuations.
Saved peer lists, completed clears and normal errors retain their source order. -/
namespace Leanux.Proofs.WG.Configuration
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes AllowedIps
universe u

def peerRemoveAllWith {m : Type → Type u} [Monad m]
    (lift : {α : Type} → WG.M α → m α) (clear : m Unit)
    (make after : PeerId → m Unit) : m Unit := do
  clear
  let dead := (← lift getDev).peerList
  for pid in dead do
    _ ← lift (branch .peerRemoveAllIter1 true)
    make pid
  _ ← lift (branch .peerRemoveAllIter1 false)
  for pid in dead do
    _ ← lift (branch .peerRemoveAllIter2 true)
    after pid
  _ ← lift (branch .peerRemoveAllIter2 false)

def devicePeersWith {m : Type → Type u} [Monad m]
    (lift : {α : Type} → WG.M α → m α) (command : PeerAttrs → m Int) (attrs : DeviceAttrs) : m Int := do
  let zero (ret : Int) : m Int := do
    _ ← lift (branch .setDevZeroKey attrs.privateKey.isSome)
    return ret
  if ← lift (branch .setDevHasPeers attrs.peers.isSome) then
    for entry in attrs.peers.getD [] do
      _ ← lift (branch .setDevPeersIter true)
      match entry with
      | .malformed =>
        _ ← lift (branch .setDevParseErr true)
        return ← zero (-EINVAL)
      | .attrs p =>
        _ ← lift (branch .setDevParseErr false)
        let ret ← command p
        if ← lift (branch .setDevSetPeerErr (ret < 0)) then return ← zero ret
    _ ← lift (branch .setDevPeersIter false)
  zero 0

def deviceKeyWith {m : Type → Type u} [Monad m]
    (lift : {α : Type} → WG.M α → m α) (lookup : Key → m (Option PeerId))
    (put remove : Option PeerId → m Unit) (precompute expire send : PeerId → m Unit)
    (next : m Int) (attrs : DeviceAttrs) : m Int := do
  if ← lift (WG.andM (branch .setDevHasPrivateKey attrs.privateKey.isSome) (branch .setDevPrivateKeyLen true)) then
    let some key := attrs.privateKey | lift (invariant "unreachable")
    if !(← lift (branch .setDevKeyUnchanged ((← lift getDev).staticIdentity.staticPrivate == key))) then
      let (pub, ok) ← lift (generatePublic key)
      if ← lift (branch .setDevGenPublic ok) then
        let some pub := pub | lift (invariant "a generated public key without a write")
        let peer ← lookup pub
        if ← lift (branch .setDevOldPeer peer.isSome) then
          put peer
          remove peer
      let d ← lift getDev
      let sendStaged ← lift (WG.andM (branch .setDevSendStagedNoIdentity !d.staticIdentity.hasIdentity)
        (branch .setDevSendStagedRunning d.running))
      lift (setStaticIdentityPrivateKey key)
      let hasIdentity := (← lift getDev).staticIdentity.hasIdentity
      let sendStaged ← lift (WG.andM (branch .setDevSendStagedKept sendStaged) (branch .setDevSendStagedHasIdentity hasIdentity))
      lift cookiePrecomputeDeviceKeys
      for pid in (← lift getDev).peerList do
        _ ← lift (branch .setDevKeyPeerIter true)
        precompute pid
        expire pid
        if ← lift (branch .setDevSendStagedPeer sendStaged) then send pid
      _ ← lift (branch .setDevKeyPeerIter false)
  next

def deviceUpdateWith {m : Type → Type u} [Monad m]
    (lift : {α : Type} → WG.M α → m α) (clear : PeerId → m Unit) (port : Nat → m Int)
    (removeAll : m Unit) (next : m Int) (attrs : DeviceAttrs) (flags : UInt32) : m Int := do
  let zero (ret : Int) : m Int := do
    _ ← lift (branch .setDevZeroKey attrs.privateKey.isSome)
    return ret
  lift (modifyDev fun d => {d with deviceUpdateGen := d.deviceUpdateGen + 1})
  if ← lift (branch .setDevFwmark attrs.fwmark.isSome) then
    lift (modifyDev fun d => {d with fwmark := attrs.fwmark.getD 0})
    for pid in (← lift getDev).peerList do
      _ ← lift (branch .setDevFwmarkPeerIter true)
      clear pid
    _ ← lift (branch .setDevFwmarkPeerIter false)
  if ← lift (branch .setDevPort attrs.listenPort.isSome) then
    let ret ← port (attrs.listenPort.getD 0)
    if ← lift (branch .setDevPortErr (ret != 0)) then return ← zero ret
  if ← lift (branch .setDevReplacePeers (flags &&& WGDEVICE_F_REPLACE_PEERS != 0)) then removeAll
  next

def setDeviceWith {m : Type → Type u} [Monad m]
    (lift : {α : Type} → WG.M α → m α) (next : UInt32 → m Int) (attrs : DeviceAttrs) : m Int := do
  let zero (ret : Int) : m Int := do
    _ ← lift (branch .setDevZeroKey attrs.privateKey.isSome)
    return ret
  let wg ← lift (lookupInterface attrs.device)
  if ← lift (branch .setDevLookupErr (wg matches .error _)) then
    let .error e := wg | lift (invariant "unreachable")
    return ← zero e
  let mut flags : UInt32 := 0
  if ← lift (branch .setDevHasFlags attrs.flags.isSome) then flags := attrs.flags.getD 0
  if ← lift (branch .setDevBadFlags (flags &&& ~~~WGDEVICE_F_ALL != 0)) then return ← zero (-EOPNOTSUPP)
  if ← lift (WG.orM (branch .setDevHasPort attrs.listenPort.isSome) (branch .setDevHasFwmark attrs.fwmark.isSome)) then
    let denied ← lift (WG.orM (branch .setDevNoNet !(← lift getDev).creatingNet) (branch .setDevNotCapable false))
    if ← lift (branch .setDevPermErr denied) then return ← zero (-EPERM)
  next flags

theorem peerRemoveAll_factor : peerRemoveAll = peerRemoveAllWith (fun {_} a => a) WG.free peerMakeDead peerRemoveAfterDead := rfl

theorem peerRemoveAllObserved_factor : peerRemoveAllObserved = peerRemoveAllWith (fun {_} a => liftWGPrefix a)
    completedFree peerMakeDeadObserved (fun pid => liftWGPrefix (peerRemoveAfterDead pid)) := rfl

theorem peerRemoveAllPrefix_factor : peerRemoveAllPrefix = peerRemoveAllWith (fun {_} a => liftWGPrefix a)
    freeAllowedIpsPrefix peerMakeDeadPrefix peerRemoveAfterDeadPrefix := rfl

theorem devicePeersSource_factor (attrs : DeviceAttrs) :
    devicePeersSource attrs = devicePeersWith (fun {_} a => a) setPeerCmd attrs := rfl

theorem devicePeersObserved_factor (attrs : DeviceAttrs) :
    devicePeersObserved attrs = devicePeersWith (fun {_} a => liftWGPrefix a) setPeerCmdObserved attrs := rfl

theorem devicePeersPrefix_factor (attrs : DeviceAttrs) :
    devicePeersPrefix attrs = devicePeersWith (fun {_} a => liftWGPrefix a) setPeerCmdPrefix attrs := rfl

theorem deviceKeySource_factor (attrs : DeviceAttrs) :
    deviceKeySource attrs = deviceKeyWith (fun {_} a => a) pubkeyLookup peerPut peerRemove
      precomputeStaticStatic expireCurrentPeerKeypairs sendStagedPackets (devicePeersSource attrs) attrs := rfl

theorem deviceKeyObserved_factor (attrs : DeviceAttrs) :
    deviceKeyObserved attrs = deviceKeyWith (fun {_} a => liftWGPrefix a)
      (fun key => liftWGPrefix (pubkeyLookup key)) (fun p => liftWGPrefix (peerPut p)) peerRemoveObserved
      (fun p => liftWGPrefix (precomputeStaticStatic p)) (fun p => liftWGPrefix (expireCurrentPeerKeypairs p))
      (fun p => liftWGPrefix (sendStagedPackets p)) (devicePeersObserved attrs) attrs := rfl

private theorem lift_bind {E α β : Type} (a : WG.M α) (f : α → WG.M β) :
    (liftWGPrefix (a >>= f) : WGPrefix E β) = (liftWGPrefix a >>= fun x => liftWGPrefix (f x)) := by
  funext w ambient
  apply ExceptT.ext
  funext h
  change runStatePrefix (liftStatePrefix (a >>= f)) w ambient h =
    runStatePrefix (liftStatePrefix a >>= fun x => liftStatePrefix (f x)) w ambient h
  rw [runStatePrefix_bind,runStatePrefix_lift,runStatePrefix_lift]
  simp only [StateT.run_bind]
  cases ha : (a.run w).run ambient <;> rfl

private theorem lift_pure {E α : Type} (x : α) :
    (liftWGPrefix (pure x) : WGPrefix E α) = pure x := rfl

private theorem lift_and {E : Type} (a b : WG.M Bool) :
    (liftWGPrefix (WG.andM a b) : WGPrefix E Bool) = andPrefix (liftWGPrefix a) (liftWGPrefix b) := by
  simp only [WG.andM,andPrefix,lift_bind,apply_ite,lift_pure]

private theorem lift_or {E : Type} (a b : WG.M Bool) :
    (liftWGPrefix (WG.orM a b) : WGPrefix E Bool) = orPrefix (liftWGPrefix a) (liftWGPrefix b) := by
  simp only [WG.orM,orPrefix,lift_bind,apply_ite,lift_pure]

theorem deviceKeyPrefix_factor (attrs : DeviceAttrs) :
    deviceKeyPrefix attrs = deviceKeyWith (fun {_} a => liftWGPrefix a) pubkeyLookupPrefix peerPutMixed peerRemovePrefix
      precomputeStaticStaticMixed expireCurrentPeerKeypairsPrefix sendStagedPacketsPrefix (devicePeersPrefix attrs) attrs := by
  simp only [deviceKeyPrefix,deviceKeyWith,rxBranch,lift_and]
  rfl

theorem deviceUpdateSource_factor (attrs : DeviceAttrs) (flags : UInt32) :
    deviceUpdateSource attrs flags = deviceUpdateWith (fun {_} a => a) clearPeerEndpointSrc setPort peerRemoveAll
      (deviceKeySource attrs) attrs flags := rfl

theorem deviceUpdateObserved_factor (attrs : DeviceAttrs) (flags : UInt32) :
    deviceUpdateObserved attrs flags = deviceUpdateWith (fun {_} a => liftWGPrefix a)
      (fun p => liftWGPrefix (clearPeerEndpointSrc p)) (fun port => liftWGPrefix (setPort port)) peerRemoveAllObserved
      (deviceKeyObserved attrs) attrs flags := rfl

theorem deviceUpdatePrefix_factor (attrs : DeviceAttrs) (flags : UInt32) :
    deviceUpdatePrefix attrs flags = deviceUpdateWith (fun {_} a => liftWGPrefix a) clearPeerEndpointSrcPrefix setPortPrefix
      peerRemoveAllPrefix (deviceKeyPrefix attrs) attrs flags := rfl

theorem setDeviceSource_factor (attrs : DeviceAttrs) :
    wgSetDeviceSource attrs = setDeviceWith (fun {_} a => a) (deviceUpdateSource attrs) attrs := rfl

theorem setDeviceObserved_factor (attrs : DeviceAttrs) :
    wgSetDeviceObserved attrs = setDeviceWith (fun {_} a => liftWGPrefix a) (deviceUpdateObserved attrs) attrs := rfl

theorem setDevicePrefix_factor (attrs : DeviceAttrs) :
    wgSetDevicePrefix attrs = setDeviceWith (fun {_} a => liftWGPrefix a) (deviceUpdatePrefix attrs) attrs := by
  simp only [wgSetDevicePrefix,setDeviceWith,rxBranch,lift_or]
  rfl

end Leanux.Proofs.WG.Configuration

namespace Leanux.Proofs.WG.Queues.RoutingJoint
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes AllowedIps Configuration

private abbrev DeviceFocused {E F α : Type} (encode : E → F) (decode : F → Option E)
    (g : WGPrefix F α) (a : WGPrefix E α) : Prop :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.Focused) encode decode g a

private theorem removeAll_projects {E F : Type} (ρ : E → Option F)
    (lift : {α : Type} → WG.M α → WGPrefix E α) (lift' : {α : Type} → WG.M α → WGPrefix F α)
    (clear : WGPrefix E Unit)
    (clear' : WGPrefix F Unit)
    (make : (PeerId) → WGPrefix E Unit)
    (make' : (PeerId) → WGPrefix F Unit)
    (after : (PeerId) → WGPrefix E Unit)
    (after' : (PeerId) → WGPrefix F Unit)
    (hl : ∀ {α : Type} (a : WG.M α), StateProjectsPrefix ρ id (lift a) (lift' a))
    (h_clear : StateProjectsPrefix ρ id (clear) (clear'))
    (h_make : ∀ x0, StateProjectsPrefix ρ id (make x0) (make' x0))
    (h_after : ∀ x0, StateProjectsPrefix ρ id (after x0) (after' x0))
    : StateProjectsPrefix ρ id (peerRemoveAllWith lift clear make after) (peerRemoveAllWith lift' clear' make' after') := by
  unfold peerRemoveAllWith
  repeat' first
    | with_reducible exact hl _
    | with_reducible exact h_clear
    | with_reducible exact h_make _
    | with_reducible exact h_after _
    | with_reducible exact (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_pure) ρ _
    | with_reducible apply StateProjectsPrefix.bind ρ id id
    | with_reducible apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_forIn) ρ
    | with_reducible apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfigurationUpdate.«0».Leanux.Proofs.WG.Queues.RoutingJoint.projects_ite) ρ
    | (maintenance_intro; try dsimp only [id_eq])
    | split

private theorem removeAll_focused {E F : Type} (encode : E → F) (decode : F → Option E) (hd : ∀ e, decode (encode e) = some e)
    (lift : {α : Type} → WG.M α → WGPrefix F α) (lift' : {α : Type} → WG.M α → WGPrefix E α)
    (clear : WGPrefix F Unit)
    (clear' : WGPrefix E Unit)
    (make : (PeerId) → WGPrefix F Unit)
    (make' : (PeerId) → WGPrefix E Unit)
    (after : (PeerId) → WGPrefix F Unit)
    (after' : (PeerId) → WGPrefix E Unit)
    (hl : ∀ {α : Type} (a : WG.M α), DeviceFocused encode decode (lift a) (lift' a))
    (h_clear : DeviceFocused encode decode (clear) (clear'))
    (h_make : ∀ x0, DeviceFocused encode decode (make x0) (make' x0))
    (h_after : ∀ x0, DeviceFocused encode decode (after x0) (after' x0))
    : DeviceFocused encode decode (peerRemoveAllWith lift clear make after) (peerRemoveAllWith lift' clear' make' after') := by
  unfold peerRemoveAllWith
  repeat' first
    | with_reducible exact hl _
    | with_reducible exact h_clear
    | with_reducible exact h_make _
    | with_reducible exact h_after _
    | with_reducible exact (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_pure) encode decode _
    | with_reducible apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_bind) encode decode hd
    | with_reducible apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_forIn) encode decode hd
    | with_reducible apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfigurationUpdate.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_ite) encode decode
    | (maintenance_intro; try dsimp only [id_eq])
    | split

private theorem peers_projects {E F : Type} (ρ : E → Option F)
    (lift : {α : Type} → WG.M α → WGPrefix E α) (lift' : {α : Type} → WG.M α → WGPrefix F α)
    (command : (PeerAttrs) → WGPrefix E Int)
    (command' : (PeerAttrs) → WGPrefix F Int)
    (hl : ∀ {α : Type} (a : WG.M α), StateProjectsPrefix ρ id (lift a) (lift' a))
    (h_command : ∀ x0, StateProjectsPrefix ρ id (command x0) (command' x0))
    (attrs : DeviceAttrs)
    : StateProjectsPrefix ρ id (devicePeersWith lift command attrs) (devicePeersWith lift' command' attrs) := by
  unfold devicePeersWith
  repeat' first
    | with_reducible exact hl _
    | with_reducible exact h_command _
    | with_reducible exact (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_pure) ρ _
    | with_reducible apply StateProjectsPrefix.bind ρ id id
    | with_reducible apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_forIn) ρ
    | with_reducible apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfigurationUpdate.«0».Leanux.Proofs.WG.Queues.RoutingJoint.projects_ite) ρ
    | (maintenance_intro; try dsimp only [id_eq])
    | split

private theorem peers_focused {E F : Type} (encode : E → F) (decode : F → Option E) (hd : ∀ e, decode (encode e) = some e)
    (lift : {α : Type} → WG.M α → WGPrefix F α) (lift' : {α : Type} → WG.M α → WGPrefix E α)
    (command : (PeerAttrs) → WGPrefix F Int)
    (command' : (PeerAttrs) → WGPrefix E Int)
    (hl : ∀ {α : Type} (a : WG.M α), DeviceFocused encode decode (lift a) (lift' a))
    (h_command : ∀ x0, DeviceFocused encode decode (command x0) (command' x0))
    (attrs : DeviceAttrs)
    : DeviceFocused encode decode (devicePeersWith lift command attrs) (devicePeersWith lift' command' attrs) := by
  unfold devicePeersWith
  repeat' first
    | with_reducible exact hl _
    | with_reducible exact h_command _
    | with_reducible exact (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_pure) encode decode _
    | with_reducible apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_bind) encode decode hd
    | with_reducible apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_forIn) encode decode hd
    | with_reducible apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfigurationUpdate.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_ite) encode decode
    | (maintenance_intro; try dsimp only [id_eq])
    | split

private theorem key_projects {E F : Type} (ρ : E → Option F)
    (lift : {α : Type} → WG.M α → WGPrefix E α) (lift' : {α : Type} → WG.M α → WGPrefix F α)
    (lookup : (Key) → WGPrefix E (Option PeerId))
    (lookup' : (Key) → WGPrefix F (Option PeerId))
    (put : (Option PeerId) → WGPrefix E Unit)
    (put' : (Option PeerId) → WGPrefix F Unit)
    (remove : (Option PeerId) → WGPrefix E Unit)
    (remove' : (Option PeerId) → WGPrefix F Unit)
    (precompute : (PeerId) → WGPrefix E Unit)
    (precompute' : (PeerId) → WGPrefix F Unit)
    (expire : (PeerId) → WGPrefix E Unit)
    (expire' : (PeerId) → WGPrefix F Unit)
    (send : (PeerId) → WGPrefix E Unit)
    (send' : (PeerId) → WGPrefix F Unit)
    (next : WGPrefix E Int)
    (next' : WGPrefix F Int)
    (hl : ∀ {α : Type} (a : WG.M α), StateProjectsPrefix ρ id (lift a) (lift' a))
    (h_lookup : ∀ x0, StateProjectsPrefix ρ id (lookup x0) (lookup' x0))
    (h_put : ∀ x0, StateProjectsPrefix ρ id (put x0) (put' x0))
    (h_remove : ∀ x0, StateProjectsPrefix ρ id (remove x0) (remove' x0))
    (h_precompute : ∀ x0, StateProjectsPrefix ρ id (precompute x0) (precompute' x0))
    (h_expire : ∀ x0, StateProjectsPrefix ρ id (expire x0) (expire' x0))
    (h_send : ∀ x0, StateProjectsPrefix ρ id (send x0) (send' x0))
    (h_next : StateProjectsPrefix ρ id (next) (next'))
    (attrs : DeviceAttrs)
    : StateProjectsPrefix ρ id (deviceKeyWith lift lookup put remove precompute expire send next attrs) (deviceKeyWith lift' lookup' put' remove' precompute' expire' send' next' attrs) := by
  unfold deviceKeyWith
  repeat' first
    | with_reducible exact hl _
    | with_reducible exact h_lookup _
    | with_reducible exact h_put _
    | with_reducible exact h_remove _
    | with_reducible exact h_precompute _
    | with_reducible exact h_expire _
    | with_reducible exact h_send _
    | with_reducible exact h_next
    | with_reducible exact (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_pure) ρ _
    | with_reducible apply StateProjectsPrefix.bind ρ id id
    | with_reducible apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_forIn) ρ
    | with_reducible apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfigurationUpdate.«0».Leanux.Proofs.WG.Queues.RoutingJoint.projects_ite) ρ
    | (maintenance_intro; try dsimp only [id_eq])
    | split

private theorem key_focused {E F : Type} (encode : E → F) (decode : F → Option E) (hd : ∀ e, decode (encode e) = some e)
    (lift : {α : Type} → WG.M α → WGPrefix F α) (lift' : {α : Type} → WG.M α → WGPrefix E α)
    (lookup : (Key) → WGPrefix F (Option PeerId))
    (lookup' : (Key) → WGPrefix E (Option PeerId))
    (put : (Option PeerId) → WGPrefix F Unit)
    (put' : (Option PeerId) → WGPrefix E Unit)
    (remove : (Option PeerId) → WGPrefix F Unit)
    (remove' : (Option PeerId) → WGPrefix E Unit)
    (precompute : (PeerId) → WGPrefix F Unit)
    (precompute' : (PeerId) → WGPrefix E Unit)
    (expire : (PeerId) → WGPrefix F Unit)
    (expire' : (PeerId) → WGPrefix E Unit)
    (send : (PeerId) → WGPrefix F Unit)
    (send' : (PeerId) → WGPrefix E Unit)
    (next : WGPrefix F Int)
    (next' : WGPrefix E Int)
    (hl : ∀ {α : Type} (a : WG.M α), DeviceFocused encode decode (lift a) (lift' a))
    (h_lookup : ∀ x0, DeviceFocused encode decode (lookup x0) (lookup' x0))
    (h_put : ∀ x0, DeviceFocused encode decode (put x0) (put' x0))
    (h_remove : ∀ x0, DeviceFocused encode decode (remove x0) (remove' x0))
    (h_precompute : ∀ x0, DeviceFocused encode decode (precompute x0) (precompute' x0))
    (h_expire : ∀ x0, DeviceFocused encode decode (expire x0) (expire' x0))
    (h_send : ∀ x0, DeviceFocused encode decode (send x0) (send' x0))
    (h_next : DeviceFocused encode decode (next) (next'))
    (attrs : DeviceAttrs)
    : DeviceFocused encode decode (deviceKeyWith lift lookup put remove precompute expire send next attrs) (deviceKeyWith lift' lookup' put' remove' precompute' expire' send' next' attrs) := by
  unfold deviceKeyWith
  repeat' first
    | with_reducible exact hl _
    | with_reducible exact h_lookup _
    | with_reducible exact h_put _
    | with_reducible exact h_remove _
    | with_reducible exact h_precompute _
    | with_reducible exact h_expire _
    | with_reducible exact h_send _
    | with_reducible exact h_next
    | with_reducible exact (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_pure) encode decode _
    | with_reducible apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_bind) encode decode hd
    | with_reducible apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_forIn) encode decode hd
    | with_reducible apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfigurationUpdate.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_ite) encode decode
    | (maintenance_intro; try dsimp only [id_eq])
    | split

private theorem update_projects {E F : Type} (ρ : E → Option F)
    (lift : {α : Type} → WG.M α → WGPrefix E α) (lift' : {α : Type} → WG.M α → WGPrefix F α)
    (clear : (PeerId) → WGPrefix E Unit)
    (clear' : (PeerId) → WGPrefix F Unit)
    (port : (Nat) → WGPrefix E Int)
    (port' : (Nat) → WGPrefix F Int)
    (removeAll : WGPrefix E Unit)
    (removeAll' : WGPrefix F Unit)
    (next : WGPrefix E Int)
    (next' : WGPrefix F Int)
    (hl : ∀ {α : Type} (a : WG.M α), StateProjectsPrefix ρ id (lift a) (lift' a))
    (h_clear : ∀ x0, StateProjectsPrefix ρ id (clear x0) (clear' x0))
    (h_port : ∀ x0, StateProjectsPrefix ρ id (port x0) (port' x0))
    (h_removeAll : StateProjectsPrefix ρ id (removeAll) (removeAll'))
    (h_next : StateProjectsPrefix ρ id (next) (next'))
    (attrs : DeviceAttrs)
    (flags : UInt32)
    : StateProjectsPrefix ρ id (deviceUpdateWith lift clear port removeAll next attrs flags) (deviceUpdateWith lift' clear' port' removeAll' next' attrs flags) := by
  unfold deviceUpdateWith
  repeat' first
    | with_reducible exact hl _
    | with_reducible exact h_clear _
    | with_reducible exact h_port _
    | with_reducible exact h_removeAll
    | with_reducible exact h_next
    | with_reducible exact (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_pure) ρ _
    | with_reducible apply StateProjectsPrefix.bind ρ id id
    | with_reducible apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_forIn) ρ
    | with_reducible apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfigurationUpdate.«0».Leanux.Proofs.WG.Queues.RoutingJoint.projects_ite) ρ
    | (maintenance_intro; try dsimp only [id_eq])
    | split

private theorem update_focused {E F : Type} (encode : E → F) (decode : F → Option E) (hd : ∀ e, decode (encode e) = some e)
    (lift : {α : Type} → WG.M α → WGPrefix F α) (lift' : {α : Type} → WG.M α → WGPrefix E α)
    (clear : (PeerId) → WGPrefix F Unit)
    (clear' : (PeerId) → WGPrefix E Unit)
    (port : (Nat) → WGPrefix F Int)
    (port' : (Nat) → WGPrefix E Int)
    (removeAll : WGPrefix F Unit)
    (removeAll' : WGPrefix E Unit)
    (next : WGPrefix F Int)
    (next' : WGPrefix E Int)
    (hl : ∀ {α : Type} (a : WG.M α), DeviceFocused encode decode (lift a) (lift' a))
    (h_clear : ∀ x0, DeviceFocused encode decode (clear x0) (clear' x0))
    (h_port : ∀ x0, DeviceFocused encode decode (port x0) (port' x0))
    (h_removeAll : DeviceFocused encode decode (removeAll) (removeAll'))
    (h_next : DeviceFocused encode decode (next) (next'))
    (attrs : DeviceAttrs)
    (flags : UInt32)
    : DeviceFocused encode decode (deviceUpdateWith lift clear port removeAll next attrs flags) (deviceUpdateWith lift' clear' port' removeAll' next' attrs flags) := by
  unfold deviceUpdateWith
  repeat' first
    | with_reducible exact hl _
    | with_reducible exact h_clear _
    | with_reducible exact h_port _
    | with_reducible exact h_removeAll
    | with_reducible exact h_next
    | with_reducible exact (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_pure) encode decode _
    | with_reducible apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_bind) encode decode hd
    | with_reducible apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_forIn) encode decode hd
    | with_reducible apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfigurationUpdate.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_ite) encode decode
    | (maintenance_intro; try dsimp only [id_eq])
    | split

private theorem device_projects {E F : Type} (ρ : E → Option F)
    (lift : {α : Type} → WG.M α → WGPrefix E α) (lift' : {α : Type} → WG.M α → WGPrefix F α)
    (next : (UInt32) → WGPrefix E Int)
    (next' : (UInt32) → WGPrefix F Int)
    (hl : ∀ {α : Type} (a : WG.M α), StateProjectsPrefix ρ id (lift a) (lift' a))
    (h_next : ∀ x0, StateProjectsPrefix ρ id (next x0) (next' x0))
    (attrs : DeviceAttrs)
    : StateProjectsPrefix ρ id (setDeviceWith lift next attrs) (setDeviceWith lift' next' attrs) := by
  unfold setDeviceWith
  repeat' first
    | with_reducible exact hl _
    | with_reducible exact h_next _
    | with_reducible exact (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_pure) ρ _
    | with_reducible apply StateProjectsPrefix.bind ρ id id
    | with_reducible apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_forIn) ρ
    | with_reducible apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfigurationUpdate.«0».Leanux.Proofs.WG.Queues.RoutingJoint.projects_ite) ρ
    | (maintenance_intro; try dsimp only [id_eq])
    | split

private theorem device_focused {E F : Type} (encode : E → F) (decode : F → Option E) (hd : ∀ e, decode (encode e) = some e)
    (lift : {α : Type} → WG.M α → WGPrefix F α) (lift' : {α : Type} → WG.M α → WGPrefix E α)
    (next : (UInt32) → WGPrefix F Int)
    (next' : (UInt32) → WGPrefix E Int)
    (hl : ∀ {α : Type} (a : WG.M α), DeviceFocused encode decode (lift a) (lift' a))
    (h_next : ∀ x0, DeviceFocused encode decode (next x0) (next' x0))
    (attrs : DeviceAttrs)
    : DeviceFocused encode decode (setDeviceWith lift next attrs) (setDeviceWith lift' next' attrs) := by
  unfold setDeviceWith
  repeat' first
    | with_reducible exact hl _
    | with_reducible exact h_next _
    | with_reducible exact (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_pure) encode decode _
    | with_reducible apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_bind) encode decode hd
    | with_reducible apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_forIn) encode decode hd
    | with_reducible apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfigurationUpdate.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_ite) encode decode
    | (maintenance_intro; try dsimp only [id_eq])
    | split

private theorem rootFree_appends (root : NodeId) : StateAppends (rootRemovePeerListsPrefix root) := by
  unfold rootRemovePeerListsPrefix
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (joint_append_head listDelPrefix
       exact (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.listDel_appends) _)
    | joint_append_step

private theorem free_appends : StateAppends freeAllowedIpsPrefix := by
  unfold freeAllowedIpsPrefix
  repeat' first
    | (joint_append_head rootRemovePeerListsPrefix; exact rootFree_appends _)
    | joint_append_step

theorem peerRemoveAllPrefix_appends : StateAppends peerRemoveAllPrefix := by
  unfold peerRemoveAllPrefix
  repeat' first
    | (joint_append_head freeAllowedIpsPrefix; exact free_appends)
    | (joint_append_head peerMakeDeadPrefix; exact peerMakeDeadPrefix_appends _)
    | (joint_append_head peerRemoveAfterDeadPrefix; exact peerRemoveAfterDeadPrefix_appends _)
    | joint_append_step

private theorem clearSource_appends (pid : PeerId) : StateAppends (clearPeerEndpointSrcPrefix pid) := by
  unfold clearPeerEndpointSrcPrefix dstCacheResetNowPrefix dstCacheResetMixed
  repeat' joint_append_step

private theorem port_appends (port : Nat) : StateAppends (setPortPrefix port) := by
  unfold setPortPrefix
  repeat' first
    | (joint_append_head clearPeerEndpointSrcPrefix; exact clearSource_appends _)
    | joint_append_step

private theorem expire_appends (pid : PeerId) : StateAppends (expireCurrentPeerKeypairsPrefix pid) := by
  unfold expireCurrentPeerKeypairsPrefix handshakeZeroPrefix resetLastSentHandshakePrefix invalidateSendingPrefix
  repeat' first
    | (joint_append_head getKeypairPrefix
       exact (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfigurationTail.«0».Leanux.Proofs.WG.Queues.RoutingJoint.readKey_appends) _)
    | (joint_append_head setKeypairPrefix
       exact (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfigurationTail.«0».Leanux.Proofs.WG.Queues.RoutingJoint.writeKey_appends) _ _)
    | joint_append_step

theorem devicePeersPrefix_appends (attrs : DeviceAttrs) : StateAppends (devicePeersPrefix attrs) := by
  rw [devicePeersPrefix_factor]
  unfold devicePeersWith
  repeat' first
    | (joint_append_head setPeerCmdPrefix; exact setPeerCmdPrefix_appends _)
    | joint_append_step

theorem deviceKeyPrefix_appends (attrs : DeviceAttrs) : StateAppends (deviceKeyPrefix attrs) := by
  rw [deviceKeyPrefix_factor]
  unfold deviceKeyWith
  repeat' first
    | (joint_append_head pubkeyLookupPrefix
       exact pubkeyLookupPrefix_appends _)
    | (joint_append_head peerRemovePrefix; exact peerRemovePrefix_appends _)
    | (joint_append_head precomputeStaticStaticMixed; exact StateAppends.focus _ _ _)
    | (joint_append_head expireCurrentPeerKeypairsPrefix; exact expire_appends _)
    | (joint_append_head sendStagedPacketsPrefix
       exact (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfigurationTail.«0».Leanux.Proofs.WG.Queues.RoutingJoint.staged_appends) _)
    | (joint_append_head devicePeersPrefix; exact devicePeersPrefix_appends _)
    | joint_append_step

theorem deviceUpdatePrefix_appends (attrs : DeviceAttrs) (flags : UInt32) :
    StateAppends (deviceUpdatePrefix attrs flags) := by
  rw [deviceUpdatePrefix_factor]
  unfold deviceUpdateWith
  repeat' first
    | (joint_append_head clearPeerEndpointSrcPrefix; exact clearSource_appends _)
    | (joint_append_head setPortPrefix; exact port_appends _)
    | (joint_append_head peerRemoveAllPrefix; exact peerRemoveAllPrefix_appends)
    | (joint_append_head deviceKeyPrefix; exact deviceKeyPrefix_appends _)
    | joint_append_step

theorem wgSetDevicePrefix_appends (attrs : DeviceAttrs) : StateAppends (wgSetDevicePrefix attrs) := by
  rw [setDevicePrefix_factor]
  unfold setDeviceWith
  repeat' first
    | (joint_append_head deviceUpdatePrefix; exact deviceUpdatePrefix_appends _ _)
    | joint_append_step

def removeAllPeers : WGPrefix Event Unit :=
  peerRemoveAllWith (fun {_} a => liftWGPrefix a)
    completedFree makeDead (fun p => access (peerRemoveAfterDeadPrefix p))

theorem removeAllPeers_routing :
    StateProjectsPrefix routingEvent id (removeAllPeers) (peerRemoveAllObserved) := by
  rw [peerRemoveAllObserved_factor]
  apply removeAll_projects routingEvent
  · exact fun {_} a => (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_lift) routingEvent a
  · exact completedFree_routing
  · exact makeDead_routing
  · exact fun p => (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_erases_frame) routingEvent (access_erases (peerRemoveAfterDeadPrefix_erases p)) (access_routing _)

private theorem removeAllPeers_rx_eq :
    peerRemoveAllWith (fun {_} a => liftWGPrefix a)
      (nativeRx (freeAllowedIpsPrefix)) (fun p => nativeRx (peerMakeDeadPrefix p)) (fun p => nativeRx (peerRemoveAfterDeadPrefix p))  =
      nativeRx (peerRemoveAllPrefix) := by
  have inner := removeAll_focused AuditEvent.lifetime AuditEvent.lifetime? (fun _ => rfl)
    (fun {_} a => liftWGPrefix a) (fun {_} a => liftWGPrefix a)
    (focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (freeAllowedIpsPrefix)) freeAllowedIpsPrefix
    (fun p => focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (peerMakeDeadPrefix p)) peerMakeDeadPrefix
    (fun p => focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (peerRemoveAfterDeadPrefix p)) peerRemoveAfterDeadPrefix
    (fun {_} a => (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_lift) AuditEvent.lifetime AuditEvent.lifetime? a)
    ⟨free_appends,rfl⟩
    (fun p => ⟨peerMakeDeadPrefix_appends p,rfl⟩)
    (fun p => ⟨peerRemoveAfterDeadPrefix_appends p,rfl⟩)

  have outer := removeAll_focused RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl)
    (fun {_} a => liftWGPrefix a) (fun {_} a => liftWGPrefix a)
    (focusStatePrefix RxHistory.Event.audit RxHistory.auditEvent (focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (freeAllowedIpsPrefix))) (focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (freeAllowedIpsPrefix))
    (fun p => focusStatePrefix RxHistory.Event.audit RxHistory.auditEvent (focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (peerMakeDeadPrefix p))) (fun p => focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (peerMakeDeadPrefix p))
    (fun p => focusStatePrefix RxHistory.Event.audit RxHistory.auditEvent (focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (peerRemoveAfterDeadPrefix p))) (fun p => focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (peerRemoveAfterDeadPrefix p))
    (fun {_} a => (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_lift) RxHistory.Event.audit RxHistory.auditEvent a)
    ⟨StateAppends.focus _ _ _,rfl⟩
    (fun p => ⟨StateAppends.focus _ _ _,rfl⟩)
    (fun p => ⟨StateAppends.focus _ _ _,rfl⟩)

  rw [peerRemoveAllPrefix_factor]
  exact outer.2.trans (congrArg (focusStatePrefix RxHistory.Event.audit RxHistory.auditEvent) inner.2)

theorem removeAllPeers_rx :
    StateProjectsPrefix rxEvent id (removeAllPeers) (nativeRx (peerRemoveAllPrefix)) := by
  rw [← removeAllPeers_rx_eq]
  apply removeAll_projects rxEvent
  · exact fun {_} a => (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_lift) rxEvent a
  · exact completed_rx freeAllowedIpsPrefix (fun _ => .clear)
  · exact makeDead_rx
  · exact fun p => access_rx _

theorem removeAllPeers_rx_product :
    ProjectsPrefix rxEvent id (liftWGObserver (removeAllPeers))
      (RxHistory.mixed (liftWGObserver (peerRemoveAllPrefix))) := by
  rw [← nativeRx_product]
  exact (removeAllPeers_rx).liftWGObserver _ _

def devicePeers (attrs : DeviceAttrs) : WGPrefix Event Int :=
  devicePeersWith (fun {_} a => liftWGPrefix a)
    setPeerCommand attrs

theorem devicePeers_routing (attrs : DeviceAttrs) :
    StateProjectsPrefix routingEvent id (devicePeers attrs) (devicePeersObserved attrs) := by
  rw [devicePeersObserved_factor attrs]
  apply peers_projects routingEvent
  · exact fun {_} a => (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_lift) routingEvent a
  · exact setPeerCommand_routing

private theorem devicePeers_rx_eq (attrs : DeviceAttrs) :
    devicePeersWith (fun {_} a => liftWGPrefix a)
      (fun a => nativeRx (setPeerCmdPrefix a)) attrs =
      nativeRx (devicePeersPrefix attrs) := by
  have inner := peers_focused AuditEvent.lifetime AuditEvent.lifetime? (fun _ => rfl)
    (fun {_} a => liftWGPrefix a) (fun {_} a => liftWGPrefix a)
    (fun a => focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (setPeerCmdPrefix a)) setPeerCmdPrefix
    (fun {_} a => (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_lift) AuditEvent.lifetime AuditEvent.lifetime? a)
    (fun a => ⟨setPeerCmdPrefix_appends a,rfl⟩)
    attrs
  have outer := peers_focused RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl)
    (fun {_} a => liftWGPrefix a) (fun {_} a => liftWGPrefix a)
    (fun a => focusStatePrefix RxHistory.Event.audit RxHistory.auditEvent (focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (setPeerCmdPrefix a))) (fun a => focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (setPeerCmdPrefix a))
    (fun {_} a => (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_lift) RxHistory.Event.audit RxHistory.auditEvent a)
    (fun a => ⟨StateAppends.focus _ _ _,rfl⟩)
    attrs
  rw [devicePeersPrefix_factor attrs]
  exact outer.2.trans (congrArg (focusStatePrefix RxHistory.Event.audit RxHistory.auditEvent) inner.2)

theorem devicePeers_rx (attrs : DeviceAttrs) :
    StateProjectsPrefix rxEvent id (devicePeers attrs) (nativeRx (devicePeersPrefix attrs)) := by
  rw [← devicePeers_rx_eq attrs]
  apply peers_projects rxEvent
  · exact fun {_} a => (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_lift) rxEvent a
  · exact setPeerCommand_rx

theorem devicePeers_rx_product (attrs : DeviceAttrs) :
    ProjectsPrefix rxEvent id (liftWGObserver (devicePeers attrs))
      (RxHistory.mixed (liftWGObserver (devicePeersPrefix attrs))) := by
  rw [← nativeRx_product]
  exact (devicePeers_rx attrs).liftWGObserver _ _

def deviceKey (attrs : DeviceAttrs) : WGPrefix Event Int :=
  deviceKeyWith (fun {_} a => liftWGPrefix a)
    (fun k => access (pubkeyLookupPrefix k)) (fun p => access (peerPutMixed p)) removePeer (fun p => access (precomputeStaticStaticMixed p)) (fun p => access (expireCurrentPeerKeypairsPrefix p)) (fun p => access (sendStagedPacketsPrefix p)) (devicePeers attrs) attrs

theorem deviceKey_routing (attrs : DeviceAttrs) :
    StateProjectsPrefix routingEvent id (deviceKey attrs) (deviceKeyObserved attrs) := by
  rw [deviceKeyObserved_factor attrs]
  apply key_projects routingEvent
  · exact fun {_} a => (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_lift) routingEvent a
  · exact fun k => (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_erases_frame) routingEvent (access_erases (pubkeyLookupPrefix_erases k)) (access_routing _)
  · exact fun p => (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_erases_frame) routingEvent (access_erases (peerPutMixed_erases p)) (access_routing _)
  · exact removePeer_routing
  · exact fun p => (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_erases_frame) routingEvent (access_erases (precomputeStaticStaticMixed_erases p)) (access_routing _)
  · exact fun p => (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_erases_frame) routingEvent (access_erases (expireCurrentPeerKeypairsPrefix_erases p)) (access_routing _)
  · exact fun p => (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_erases_frame) routingEvent (access_erases (sendStagedPacketsPrefix_erases p)) (access_routing _)
  · exact devicePeers_routing attrs

private theorem deviceKey_rx_eq (attrs : DeviceAttrs) :
    deviceKeyWith (fun {_} a => liftWGPrefix a)
      (fun k => nativeRx (pubkeyLookupPrefix k)) (fun p => nativeRx (peerPutMixed p)) (fun p => nativeRx (peerRemovePrefix p)) (fun p => nativeRx (precomputeStaticStaticMixed p)) (fun p => nativeRx (expireCurrentPeerKeypairsPrefix p)) (fun p => nativeRx (sendStagedPacketsPrefix p)) (nativeRx ((devicePeersPrefix attrs))) attrs =
      nativeRx (deviceKeyPrefix attrs) := by
  have inner := key_focused AuditEvent.lifetime AuditEvent.lifetime? (fun _ => rfl)
    (fun {_} a => liftWGPrefix a) (fun {_} a => liftWGPrefix a)
    (fun k => focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (pubkeyLookupPrefix k)) pubkeyLookupPrefix
    (fun p => focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (peerPutMixed p)) peerPutMixed
    (fun p => focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (peerRemovePrefix p)) peerRemovePrefix
    (fun p => focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (precomputeStaticStaticMixed p)) precomputeStaticStaticMixed
    (fun p => focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (expireCurrentPeerKeypairsPrefix p)) expireCurrentPeerKeypairsPrefix
    (fun p => focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (sendStagedPacketsPrefix p)) sendStagedPacketsPrefix
    (focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? ((devicePeersPrefix attrs))) (devicePeersPrefix attrs)
    (fun {_} a => (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_lift) AuditEvent.lifetime AuditEvent.lifetime? a)
    (fun k => ⟨pubkeyLookupPrefix_appends k,rfl⟩)
    (fun p => ⟨StateAppends.focus _ _ _,rfl⟩)
    (fun p => ⟨peerRemovePrefix_appends p,rfl⟩)
    (fun p => ⟨StateAppends.focus _ _ _,rfl⟩)
    (fun p => ⟨expire_appends p,rfl⟩)
    (fun p => ⟨(pinned_const _private.Leanux.Proofs.WG.Queues.JointConfigurationTail.«0».Leanux.Proofs.WG.Queues.RoutingJoint.staged_appends) p,rfl⟩)
    ⟨devicePeersPrefix_appends attrs,rfl⟩
    attrs
  have outer := key_focused RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl)
    (fun {_} a => liftWGPrefix a) (fun {_} a => liftWGPrefix a)
    (fun k => focusStatePrefix RxHistory.Event.audit RxHistory.auditEvent (focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (pubkeyLookupPrefix k))) (fun k => focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (pubkeyLookupPrefix k))
    (fun p => focusStatePrefix RxHistory.Event.audit RxHistory.auditEvent (focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (peerPutMixed p))) (fun p => focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (peerPutMixed p))
    (fun p => focusStatePrefix RxHistory.Event.audit RxHistory.auditEvent (focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (peerRemovePrefix p))) (fun p => focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (peerRemovePrefix p))
    (fun p => focusStatePrefix RxHistory.Event.audit RxHistory.auditEvent (focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (precomputeStaticStaticMixed p))) (fun p => focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (precomputeStaticStaticMixed p))
    (fun p => focusStatePrefix RxHistory.Event.audit RxHistory.auditEvent (focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (expireCurrentPeerKeypairsPrefix p))) (fun p => focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (expireCurrentPeerKeypairsPrefix p))
    (fun p => focusStatePrefix RxHistory.Event.audit RxHistory.auditEvent (focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (sendStagedPacketsPrefix p))) (fun p => focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (sendStagedPacketsPrefix p))
    (focusStatePrefix RxHistory.Event.audit RxHistory.auditEvent (focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? ((devicePeersPrefix attrs)))) (focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? ((devicePeersPrefix attrs)))
    (fun {_} a => (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_lift) RxHistory.Event.audit RxHistory.auditEvent a)
    (fun k => ⟨StateAppends.focus _ _ _,rfl⟩)
    (fun p => ⟨StateAppends.focus _ _ _,rfl⟩)
    (fun p => ⟨StateAppends.focus _ _ _,rfl⟩)
    (fun p => ⟨StateAppends.focus _ _ _,rfl⟩)
    (fun p => ⟨StateAppends.focus _ _ _,rfl⟩)
    (fun p => ⟨StateAppends.focus _ _ _,rfl⟩)
    ⟨StateAppends.focus _ _ _,rfl⟩
    attrs
  rw [deviceKeyPrefix_factor attrs]
  exact outer.2.trans (congrArg (focusStatePrefix RxHistory.Event.audit RxHistory.auditEvent) inner.2)

theorem deviceKey_rx (attrs : DeviceAttrs) :
    StateProjectsPrefix rxEvent id (deviceKey attrs) (nativeRx (deviceKeyPrefix attrs)) := by
  rw [← deviceKey_rx_eq attrs]
  apply key_projects rxEvent
  · exact fun {_} a => (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_lift) rxEvent a
  · exact fun k => access_rx _
  · exact fun p => access_rx _
  · exact removePeer_rx
  · exact fun p => access_rx _
  · exact fun p => access_rx _
  · exact fun p => access_rx _
  · exact devicePeers_rx attrs

theorem deviceKey_rx_product (attrs : DeviceAttrs) :
    ProjectsPrefix rxEvent id (liftWGObserver (deviceKey attrs))
      (RxHistory.mixed (liftWGObserver (deviceKeyPrefix attrs))) := by
  rw [← nativeRx_product]
  exact (deviceKey_rx attrs).liftWGObserver _ _

def deviceUpdate (attrs : DeviceAttrs) (flags : UInt32) : WGPrefix Event Int :=
  deviceUpdateWith (fun {_} a => liftWGPrefix a)
    (fun p => access (clearPeerEndpointSrcPrefix p)) (fun port => access (setPortPrefix port)) removeAllPeers (deviceKey attrs) attrs flags

theorem deviceUpdate_routing (attrs : DeviceAttrs) (flags : UInt32) :
    StateProjectsPrefix routingEvent id (deviceUpdate attrs flags) (deviceUpdateObserved attrs flags) := by
  rw [deviceUpdateObserved_factor attrs flags]
  apply update_projects routingEvent
  · exact fun {_} a => (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_lift) routingEvent a
  · exact fun p => (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_erases_frame) routingEvent (access_erases (clearPeerEndpointSrcPrefix_erases p)) (access_routing _)
  · exact fun port => (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_erases_frame) routingEvent (access_erases (setPortPrefix_erases port)) (access_routing _)
  · exact removeAllPeers_routing
  · exact deviceKey_routing attrs

private theorem deviceUpdate_rx_eq (attrs : DeviceAttrs) (flags : UInt32) :
    deviceUpdateWith (fun {_} a => liftWGPrefix a)
      (fun p => nativeRx (clearPeerEndpointSrcPrefix p)) (fun port => nativeRx (setPortPrefix port)) (nativeRx (peerRemoveAllPrefix)) (nativeRx ((deviceKeyPrefix attrs))) attrs flags =
      nativeRx (deviceUpdatePrefix attrs flags) := by
  have inner := update_focused AuditEvent.lifetime AuditEvent.lifetime? (fun _ => rfl)
    (fun {_} a => liftWGPrefix a) (fun {_} a => liftWGPrefix a)
    (fun p => focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (clearPeerEndpointSrcPrefix p)) clearPeerEndpointSrcPrefix
    (fun port => focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (setPortPrefix port)) setPortPrefix
    (focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (peerRemoveAllPrefix)) peerRemoveAllPrefix
    (focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? ((deviceKeyPrefix attrs))) (deviceKeyPrefix attrs)
    (fun {_} a => (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_lift) AuditEvent.lifetime AuditEvent.lifetime? a)
    (fun p => ⟨clearSource_appends p,rfl⟩)
    (fun port => ⟨port_appends port,rfl⟩)
    ⟨peerRemoveAllPrefix_appends,rfl⟩
    ⟨deviceKeyPrefix_appends attrs,rfl⟩
    attrs flags
  have outer := update_focused RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl)
    (fun {_} a => liftWGPrefix a) (fun {_} a => liftWGPrefix a)
    (fun p => focusStatePrefix RxHistory.Event.audit RxHistory.auditEvent (focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (clearPeerEndpointSrcPrefix p))) (fun p => focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (clearPeerEndpointSrcPrefix p))
    (fun port => focusStatePrefix RxHistory.Event.audit RxHistory.auditEvent (focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (setPortPrefix port))) (fun port => focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (setPortPrefix port))
    (focusStatePrefix RxHistory.Event.audit RxHistory.auditEvent (focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (peerRemoveAllPrefix))) (focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (peerRemoveAllPrefix))
    (focusStatePrefix RxHistory.Event.audit RxHistory.auditEvent (focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? ((deviceKeyPrefix attrs)))) (focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? ((deviceKeyPrefix attrs)))
    (fun {_} a => (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_lift) RxHistory.Event.audit RxHistory.auditEvent a)
    (fun p => ⟨StateAppends.focus _ _ _,rfl⟩)
    (fun port => ⟨StateAppends.focus _ _ _,rfl⟩)
    ⟨StateAppends.focus _ _ _,rfl⟩
    ⟨StateAppends.focus _ _ _,rfl⟩
    attrs flags
  rw [deviceUpdatePrefix_factor attrs flags]
  exact outer.2.trans (congrArg (focusStatePrefix RxHistory.Event.audit RxHistory.auditEvent) inner.2)

theorem deviceUpdate_rx (attrs : DeviceAttrs) (flags : UInt32) :
    StateProjectsPrefix rxEvent id (deviceUpdate attrs flags) (nativeRx (deviceUpdatePrefix attrs flags)) := by
  rw [← deviceUpdate_rx_eq attrs flags]
  apply update_projects rxEvent
  · exact fun {_} a => (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_lift) rxEvent a
  · exact fun p => access_rx _
  · exact fun port => access_rx _
  · exact removeAllPeers_rx
  · exact deviceKey_rx attrs

theorem deviceUpdate_rx_product (attrs : DeviceAttrs) (flags : UInt32) :
    ProjectsPrefix rxEvent id (liftWGObserver (deviceUpdate attrs flags))
      (RxHistory.mixed (liftWGObserver (deviceUpdatePrefix attrs flags))) := by
  rw [← nativeRx_product]
  exact (deviceUpdate_rx attrs flags).liftWGObserver _ _

def setDevice (attrs : DeviceAttrs) : WGPrefix Event Int :=
  setDeviceWith (fun {_} a => liftWGPrefix a)
    (deviceUpdate attrs) attrs

theorem setDevice_routing (attrs : DeviceAttrs) :
    StateProjectsPrefix routingEvent id (setDevice attrs) (wgSetDeviceObserved attrs) := by
  rw [setDeviceObserved_factor attrs]
  apply device_projects routingEvent
  · exact fun {_} a => (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_lift) routingEvent a
  · exact deviceUpdate_routing attrs

private theorem setDevice_rx_eq (attrs : DeviceAttrs) :
    setDeviceWith (fun {_} a => liftWGPrefix a)
      (fun flags => nativeRx ((deviceUpdatePrefix attrs) flags)) attrs =
      nativeRx (wgSetDevicePrefix attrs) := by
  have inner := device_focused AuditEvent.lifetime AuditEvent.lifetime? (fun _ => rfl)
    (fun {_} a => liftWGPrefix a) (fun {_} a => liftWGPrefix a)
    (fun flags => focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? ((deviceUpdatePrefix attrs) flags)) (deviceUpdatePrefix attrs)
    (fun {_} a => (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_lift) AuditEvent.lifetime AuditEvent.lifetime? a)
    (fun flags => ⟨deviceUpdatePrefix_appends attrs flags,rfl⟩)
    attrs
  have outer := device_focused RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl)
    (fun {_} a => liftWGPrefix a) (fun {_} a => liftWGPrefix a)
    (fun flags => focusStatePrefix RxHistory.Event.audit RxHistory.auditEvent (focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? ((deviceUpdatePrefix attrs) flags))) (fun flags => focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? ((deviceUpdatePrefix attrs) flags))
    (fun {_} a => (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_lift) RxHistory.Event.audit RxHistory.auditEvent a)
    (fun flags => ⟨StateAppends.focus _ _ _,rfl⟩)
    attrs
  rw [setDevicePrefix_factor attrs]
  exact outer.2.trans (congrArg (focusStatePrefix RxHistory.Event.audit RxHistory.auditEvent) inner.2)

theorem setDevice_rx (attrs : DeviceAttrs) :
    StateProjectsPrefix rxEvent id (setDevice attrs) (nativeRx (wgSetDevicePrefix attrs)) := by
  rw [← setDevice_rx_eq attrs]
  apply device_projects rxEvent
  · exact fun {_} a => (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_lift) rxEvent a
  · exact deviceUpdate_rx attrs

theorem setDevice_rx_product (attrs : DeviceAttrs) :
    ProjectsPrefix rxEvent id (liftWGObserver (setDevice attrs))
      (RxHistory.mixed (liftWGObserver (wgSetDevicePrefix attrs))) := by
  rw [← nativeRx_product]
  exact (setDevice_rx attrs).liftWGObserver _ _

/-- One actual native execution, including every Stop and normal errno result. -/
theorem setDevice_erases (attrs : DeviceAttrs) :
    ErasesStatePrefix (setDevice attrs) (WG.wgSetDevice attrs) := by
  intro w ambient h
  have hp := congrArg Prod.fst (setDevice_routing attrs w ambient h)
  have he := wgSetDeviceObserved_erases attrs w ambient (h.filterMap routingEvent)
  have same := hp.symm.trans he
  change ((runWGPrefix (setDevice attrs) w ambient h).1.map
    (fun ((x,v),a) => ((x,v),a))) = _ at same
  change (runWGPrefix (setDevice attrs) w ambient h).1 = _
  cases hr : (runWGPrefix (setDevice attrs) w ambient h).1 <;>
    simpa only [hr,Except.map] using same

end Leanux.Proofs.WG.Queues.RoutingJoint
