import Leanux.Proofs.WG.Lifetimes.ConfigurationLeaves
import Leanux.Proofs.WG.Lifetimes.PeerAllocation
import Leanux.Proofs.WG.Configuration.PeerSource

/-! Complete original peer configuration. Ordinary negative returns retain
earlier mutations and run the source put/zero tail; Stops skip that continuation.
The keepalive setter writes the peer captured before its scalar branch records,
without an extra getter or a reference-affiliation premise. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Leanux.Proofs.WG.Configuration
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

def configureKeepaliveValuePrefix (pid : PeerId) (running : Bool) (interval : Nat) : MixedM Bool := do
  let p ← getPeerMixed pid
  let send ← liftWGPrefix (WG.andM (branch .peerKeepaliveWasZero (p.persistentKeepaliveInterval == 0))
    (WG.andM (branch .peerKeepaliveNonzero (interval != 0)) (branch .peerKeepaliveRunning running)))
  setPeerMixed pid {p with persistentKeepaliveInterval := interval}
  return send

def configureKeepalivePrefix (pid : PeerId) (running : Bool) (interval : Nat) : MixedM Unit := do
  let send ← configureKeepaliveValuePrefix pid running interval
  if ← liftWGPrefix (branch .peerSendKeepalive send) then sendKeepalivePrefix pid

def peerConfigTailPrefix (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) : MixedM Int := do
  let out (peer : Option PeerId) (ret : Int) : MixedM Int := do
    peerPutMixed peer
    _ ← liftWGPrefix (branch .peerZeroPsk a.presharedKey.isSome)
    return ret
  let mut ret : Int := 0
  if ← liftWGPrefix (branch .peerHasAips a.allowedIps.isSome) then
    for entry in a.allowedIps.getD [] do
      _ ← liftWGPrefix (branch .peerAipsIter true)
      match entry with
      | .malformed =>
        _ ← liftWGPrefix (branch .peerAipParseErr true)
        return ← out peer (-EINVAL)
      | .attrs ip =>
        _ ← liftWGPrefix (branch .peerAipParseErr false)
        ret ← setAllowedipPrefix pid ip
        if ← liftWGPrefix (branch .peerAipErr (ret < 0)) then return ← out peer ret
    _ ← liftWGPrefix (branch .peerAipsIter false)
  let running := (← liftWGPrefix getDev).running
  if ← liftWGPrefix (branch .peerHasKeepalive a.keepalive.isSome) then
    configureKeepalivePrefix pid running (a.keepalive.getD 0)
  if ← liftWGPrefix (branch .peerRunning running) then sendStagedPacketsPrefix pid
  out peer ret

def peerConfigUpdatePrefix (a : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) : MixedM Int := do
  let out (peer : Option PeerId) (ret : Int) : MixedM Int := do
    peerPutMixed peer
    _ ← liftWGPrefix (branch .peerZeroPsk a.presharedKey.isSome)
    return ret
  if ← liftWGPrefix (branch .peerRemoveMe (flags &&& WGPEER_F_REMOVE_ME != 0)) then
    peerRemovePrefix peer
    return ← out peer 0
  if ← liftWGPrefix (branch .peerSetPsk psk.isSome) then
    modifyPeerKeysPrefix pid fun p => {p with presharedKey := psk.getD []}
  if ← liftWGPrefix (branch .peerHasEndpoint a.endpoint.isSome) then
    let some e := a.endpoint | liftWGPrefix (invariant "unreachable")
    if ← liftWGPrefix (WG.andM (branch .peerEndpointV4Len (e.len == 16)) (branch .peerEndpointV4Family (e.family == AF_INET))) then
      setPeerEndpointPrefix pid {family := e.family, addr := e.addr, port := e.port}
    else if ← liftWGPrefix (WG.andM (branch .peerEndpointV6Len (e.len == 28)) (branch .peerEndpointV6Family (e.family == AF_INET6))) then
      setPeerEndpointPrefix pid {family := e.family, addr := e.addr, port := e.port, scope := e.scope, flowinfo := e.flowinfo}
  if ← liftWGPrefix (branch .peerReplaceAips (flags &&& WGPEER_F_REPLACE_ALLOWEDIPS != 0)) then removeByPeerPrefix pid
  peerConfigTailPrefix a peer pid

def setPeerCmdPrefix (a : PeerAttrs) : MixedM Int := do
  let out (peer : Option PeerId) (ret : Int) : MixedM Int := do
    peerPutMixed peer
    _ ← liftWGPrefix (branch .peerZeroPsk a.presharedKey.isSome)
    return ret
  if !(← liftWGPrefix (WG.andM (branch .peerHasPubkey a.publicKey.isSome) (branch .peerPubkeyLen true))) then
    return ← out none (-EINVAL)
  let some publicKey := a.publicKey | liftWGPrefix (invariant "unreachable")
  let psk ← do
    if ← liftWGPrefix (WG.andM (branch .peerHasPsk a.presharedKey.isSome) (branch .peerPskLen true)) then pure a.presharedKey
    else pure none
  let mut flags : UInt32 := 0
  if ← liftWGPrefix (branch .peerHasFlags a.flags.isSome) then flags := a.flags.getD 0
  if ← liftWGPrefix (branch .peerBadFlags (flags &&& ~~~WGPEER_F_ALL != 0)) then return ← out none (-EOPNOTSUPP)
  if ← liftWGPrefix (branch .peerHasProtocol a.protocolVersion.isSome) then
    if ← liftWGPrefix (branch .peerBadProtocol (a.protocolVersion != some 1)) then return ← out none (-EPFNOSUPPORT)
  let mut peer ← pubkeyLookupPrefix publicKey
  if ← liftWGPrefix (branch .peerNotFound peer.isNone) then
    if ← liftWGPrefix (branch .peerNewRemoveOrUpdate (flags &&& (WGPEER_F_REMOVE_ME ||| WGPEER_F_UPDATE_ONLY) != 0)) then
      return ← out none 0
    flags := flags &&& ~~~WGPEER_F_REPLACE_ALLOWEDIPS
    let id := (← liftWGPrefix getDev).staticIdentity
    if ← liftWGPrefix (WG.andM (branch .peerSelfHasIdentity id.hasIdentity) (branch .peerSelfKeyMatch (publicKey == id.staticPublic))) then
      return ← out none 0
    match ← peerCreateMixed publicKey psk with
    | .error e =>
      _ ← liftWGPrefix (branch .peerCreateErr true)
      return ← out none e
    | .ok pid =>
      _ ← liftWGPrefix (branch .peerCreateErr false)
      peerGetMixed pid
      peer := some pid
  let some pid := peer | liftWGPrefix (invariant "set_peer without a peer")
  peerConfigUpdatePrefix a peer flags psk pid

theorem peerConfigTailPrefix_erases (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    ErasesStatePrefix (peerConfigTailPrefix a peer pid) (peerConfigTailSource a peer pid) := by
  unfold peerConfigTailPrefix peerConfigTailSource configureKeepalivePrefix configureKeepaliveValuePrefix
  simp only [bind_assoc, pure_bind]
  repeat' first
    | with_reducible exact peerPutMixed_erases _
    | with_reducible exact pubkeyLookupPrefix_erases _
    | with_reducible exact peerCreateMixed_erases _ _
    | with_reducible exact peerGetMixed_erases _
    | with_reducible exact peerRemovePrefix_erases _
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact setPeerMixed_erases _ _
    | with_reducible exact setPeerEndpointPrefix_erases _ _
    | with_reducible exact removeByPeerPrefix_erases _
    | with_reducible exact setAllowedipPrefix_erases _ _
    | with_reducible exact sendKeepalivePrefix_erases _
    | with_reducible exact sendStagedPacketsPrefix_erases _
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_forIn
    | with_reducible apply erasesStatePrefix_bind
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals try simp_all
  all_goals try simp only [map_eq_pure_bind]
  all_goals
    repeat' first
      | with_reducible exact peerPutMixed_erases _
      | with_reducible exact pubkeyLookupPrefix_erases _
      | with_reducible exact peerCreateMixed_erases _ _
      | with_reducible exact peerGetMixed_erases _
      | with_reducible exact peerRemovePrefix_erases _
      | with_reducible exact getPeerMixed_erases _
      | with_reducible exact setPeerMixed_erases _ _
      | with_reducible exact setPeerEndpointPrefix_erases _ _
      | with_reducible exact removeByPeerPrefix_erases _
      | with_reducible exact setAllowedipPrefix_erases _ _
      | with_reducible exact sendKeepalivePrefix_erases _
      | with_reducible exact sendStagedPacketsPrefix_erases _
      | exact erasesStatePrefix_lift _
      | with_reducible exact erasesStatePrefix_pure _
      | with_reducible apply erasesStatePrefix_forIn
      | with_reducible apply erasesStatePrefix_bind
      | (with_reducible intro x; try dsimp only)
      | (with_reducible split)

theorem peerConfigUpdatePrefix_erases (a : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    ErasesStatePrefix (peerConfigUpdatePrefix a peer flags psk pid) (peerConfigUpdateSource a peer flags psk pid) := by
  unfold peerConfigUpdatePrefix peerConfigUpdateSource modifyPeerKeysPrefix
  simp only [bind_assoc]
  repeat' first
    | with_reducible exact peerConfigTailPrefix_erases _ _ _
    | with_reducible exact peerPutMixed_erases _
    | with_reducible exact pubkeyLookupPrefix_erases _
    | with_reducible exact peerCreateMixed_erases _ _
    | with_reducible exact peerGetMixed_erases _
    | with_reducible exact peerRemovePrefix_erases _
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact setPeerMixed_erases _ _
    | with_reducible exact setPeerEndpointPrefix_erases _ _
    | with_reducible exact removeByPeerPrefix_erases _
    | with_reducible exact setAllowedipPrefix_erases _ _
    | with_reducible exact sendKeepalivePrefix_erases _
    | with_reducible exact sendStagedPacketsPrefix_erases _
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_forIn
    | with_reducible apply erasesStatePrefix_bind
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals try simp_all
  all_goals try simp only [map_eq_pure_bind]
  all_goals
    repeat' first
      | with_reducible exact peerConfigTailPrefix_erases _ _ _
      | with_reducible exact peerPutMixed_erases _
      | with_reducible exact pubkeyLookupPrefix_erases _
      | with_reducible exact peerCreateMixed_erases _ _
      | with_reducible exact peerGetMixed_erases _
      | with_reducible exact peerRemovePrefix_erases _
      | with_reducible exact getPeerMixed_erases _
      | with_reducible exact setPeerMixed_erases _ _
      | with_reducible exact setPeerEndpointPrefix_erases _ _
      | with_reducible exact removeByPeerPrefix_erases _
      | with_reducible exact setAllowedipPrefix_erases _ _
      | with_reducible exact sendKeepalivePrefix_erases _
      | with_reducible exact sendStagedPacketsPrefix_erases _
      | exact erasesStatePrefix_lift _
      | with_reducible exact erasesStatePrefix_pure _
      | with_reducible apply erasesStatePrefix_forIn
      | with_reducible apply erasesStatePrefix_bind
      | (with_reducible intro x; try dsimp only)
      | (with_reducible split)

theorem setPeerCmdPrefix_erases (a : PeerAttrs) : ErasesStatePrefix (setPeerCmdPrefix a) (setPeerCmd a) := by
  rw [← setPeerCmd_source]
  unfold setPeerCmdPrefix setPeerCmdSource
  repeat' first
    | contradiction
    | maintenance_impossible_match
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_erases_bind
    | (maintenance_head peerConfigUpdatePrefix; exact peerConfigUpdatePrefix_erases _ _ _ _ _)
    | (maintenance_head peerPutMixed; exact peerPutMixed_erases _)
    | (maintenance_head pubkeyLookupPrefix; exact pubkeyLookupPrefix_erases _)
    | (maintenance_head peerCreateMixed; exact peerCreateMixed_erases _ _)
    | (maintenance_head peerGetMixed; exact peerGetMixed_erases _)
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro
    | rfl

theorem configureKeepaliveValuePrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (pid : PeerId) (running : Bool) (interval : Nat) :
    AmbientSpec I P (configureKeepaliveValuePrefix pid running interval) (fun _ => P) := by
  have hb (d : Decision) (b : Bool) : SameWGStore (branch d b) :=
    fun initial => hoare_liftAmbient (AmbientM.branch d b) (fun w => wgStoreView w = initial)
  unfold configureKeepaliveValuePrefix
  apply StatePrefixEnsures.bind (c.getPeer P pid)
  intro p
  apply StatePrefixEnsures.bind (c.store (fun s => P s ∧ s.1.slots pid = some p.internalId) _
    (andM_sameView (hb _ _) (andM_sameView (hb _ _) (hb _ _))))
  intro send
  exact StatePrefixEnsures.bind (c.setPeer P pid {p with persistentKeepaliveInterval := interval})
    (fun _ => c.pure P send)

theorem configureKeepalivePrefix_preserves (c : AmbientContracts I) (ht : TxContracts I)
    (pid : PeerId) (running : Bool) (interval : Nat) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (configureKeepalivePrefix pid running interval) := by
  have hb (d : Decision) (b : Bool) : SameWGStore (branch d b) :=
    fun initial => hoare_liftAmbient (AmbientM.branch d b) (fun w => wgStoreView w = initial)
  unfold configureKeepalivePrefix
  apply StatePrefixEnsures.bind (AmbientContracts.drop (configureKeepaliveValuePrefix_spec c (fun _ => True) pid running interval))
  intro send
  apply StatePrefixEnsures.bind (AmbientContracts.drop (c.store (fun _ => True) _ (hb _ _)))
  intro yes
  split
  · exact sendKeepalivePrefix_preserves_ambient c ht pid
  · exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)

structure ConfigurationPeerContracts (I : List LifetimeEvent → WGWorld → Prop) : Prop where
  nodes : NodeAllocationStable I
  removal : PeerRemovalContracts I
  tx : TxContracts I
  create : ∀ key psk, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (peerCreateMixed key psk)

theorem allocationConfigurationPeer : ConfigurationPeerContracts AllocationInv :=
  ⟨allocationNodeAllocationStable, allocationPeerRemoval, allocationTx, peerCreateMixed_preserves⟩

theorem peerConfigTailPrefix_preserves (c : AmbientContracts I) (r : ConfigurationPeerContracts I)
    (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (peerConfigTailPrefix a peer pid) := by
  have hb (d : Decision) (b : Bool) : SameWGStore (branch d b) :=
    fun initial => hoare_liftAmbient (AmbientM.branch d b) (fun w => wgStoreView w = initial)
  change StatePrefixEnsures _ _ _ _
  unfold peerConfigTailPrefix
  repeat' first
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head pubkeyLookupPrefix; exact pubkeyLookupPrefix_preserves_ambient c _)
    | (maintenance_head peerCreateMixed; exact r.create _ _)
    | (maintenance_head peerGetMixed; exact c.peerGet _)
    | (maintenance_head peerRemovePrefix; exact peerRemovePrefix_preserves c r.removal _)
    | (maintenance_head modifyPeerKeysPrefix; exact AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) _ _ (fun _ => rfl)))
    | (maintenance_head setPeerEndpointPrefix; exact AmbientContracts.drop (setPeerEndpointPrefix_spec c (fun _ => True) _ _))
    | (maintenance_head removeByPeerPrefix; exact removeByPeerPrefix_preserves c r.removal.allowedIps.nodes _)
    | (maintenance_head setAllowedipPrefix; exact setAllowedipPrefix_preserves c r.nodes _ _)
    | (maintenance_head configureKeepalivePrefix; exact configureKeepalivePrefix_preserves c r.tx _ _ _)
    | (maintenance_head sendStagedPacketsPrefix; exact sendStagedPacketsPrefix_preserves_ambient c r.tx _)
    | (maintenance_lift_action_head invariant; exact AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.invariant _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head branch; exact AmbientContracts.drop (c.store (fun _ => True) _ (hb _ _)))
    | (maintenance_lift_action_head getDev; exact AmbientContracts.drop (c.store (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head WG.andM; exact AmbientContracts.drop (c.store (fun _ => True) _ (andM_sameView (hb _ _) (hb _ _))))
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
  all_goals try simp_all

theorem peerConfigUpdatePrefix_preserves (c : AmbientContracts I) (r : ConfigurationPeerContracts I)
    (a : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (peerConfigUpdatePrefix a peer flags psk pid) := by
  have hb (d : Decision) (b : Bool) : SameWGStore (branch d b) :=
    fun initial => hoare_liftAmbient (AmbientM.branch d b) (fun w => wgStoreView w = initial)
  change StatePrefixEnsures _ _ _ _
  unfold peerConfigUpdatePrefix
  repeat' first
    | (maintenance_head peerConfigTailPrefix; exact peerConfigTailPrefix_preserves c r _ _ _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head pubkeyLookupPrefix; exact pubkeyLookupPrefix_preserves_ambient c _)
    | (maintenance_head peerCreateMixed; exact r.create _ _)
    | (maintenance_head peerGetMixed; exact c.peerGet _)
    | (maintenance_head peerRemovePrefix; exact peerRemovePrefix_preserves c r.removal _)
    | (maintenance_head modifyPeerKeysPrefix; exact AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) _ _ (fun _ => rfl)))
    | (maintenance_head setPeerEndpointPrefix; exact AmbientContracts.drop (setPeerEndpointPrefix_spec c (fun _ => True) _ _))
    | (maintenance_head removeByPeerPrefix; exact removeByPeerPrefix_preserves c r.removal.allowedIps.nodes _)
    | (maintenance_head setAllowedipPrefix; exact setAllowedipPrefix_preserves c r.nodes _ _)
    | (maintenance_head configureKeepalivePrefix; exact configureKeepalivePrefix_preserves c r.tx _ _ _)
    | (maintenance_head sendStagedPacketsPrefix; exact sendStagedPacketsPrefix_preserves_ambient c r.tx _)
    | (maintenance_lift_action_head invariant; exact AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.invariant _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head branch; exact AmbientContracts.drop (c.store (fun _ => True) _ (hb _ _)))
    | (maintenance_lift_action_head getDev; exact AmbientContracts.drop (c.store (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head WG.andM; exact AmbientContracts.drop (c.store (fun _ => True) _ (andM_sameView (hb _ _) (hb _ _))))
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
  all_goals try simp_all

theorem setPeerCmdPrefix_preserves (c : AmbientContracts I) (r : ConfigurationPeerContracts I)
    (a : PeerAttrs) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (setPeerCmdPrefix a) := by
  have hb (d : Decision) (b : Bool) : SameWGStore (branch d b) :=
    fun initial => hoare_liftAmbient (AmbientM.branch d b) (fun w => wgStoreView w = initial)
  change StatePrefixEnsures _ _ _ _
  unfold setPeerCmdPrefix
  repeat' first
    | (maintenance_head peerConfigUpdatePrefix; exact peerConfigUpdatePrefix_preserves c r _ _ _ _ _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head pubkeyLookupPrefix; exact pubkeyLookupPrefix_preserves_ambient c _)
    | (maintenance_head peerCreateMixed; exact r.create _ _)
    | (maintenance_head peerGetMixed; exact c.peerGet _)
    | (maintenance_head peerRemovePrefix; exact peerRemovePrefix_preserves c r.removal _)
    | (maintenance_head modifyPeerKeysPrefix; exact AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) _ _ (fun _ => rfl)))
    | (maintenance_head setPeerEndpointPrefix; exact AmbientContracts.drop (setPeerEndpointPrefix_spec c (fun _ => True) _ _))
    | (maintenance_head removeByPeerPrefix; exact removeByPeerPrefix_preserves c r.removal.allowedIps.nodes _)
    | (maintenance_head setAllowedipPrefix; exact setAllowedipPrefix_preserves c r.nodes _ _)
    | (maintenance_head configureKeepalivePrefix; exact configureKeepalivePrefix_preserves c r.tx _ _ _)
    | (maintenance_head sendStagedPacketsPrefix; exact sendStagedPacketsPrefix_preserves_ambient c r.tx _)
    | (maintenance_lift_action_head invariant; exact AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.invariant _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head branch; exact AmbientContracts.drop (c.store (fun _ => True) _ (hb _ _)))
    | (maintenance_lift_action_head getDev; exact AmbientContracts.drop (c.store (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head WG.andM; exact AmbientContracts.drop (c.store (fun _ => True) _ (andM_sameView (hb _ _) (hb _ _))))
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
  all_goals try simp_all
theorem configureKeepaliveValuePrefix_spec_product (c : ProductAmbientContracts I) (P : IdentityView → Prop)
    (pid : PeerId) (running : Bool) (interval : Nat) :
    ProductAmbientSpec I P (liftWGObserver (configureKeepaliveValuePrefix pid running interval)) (fun _ => P) := by
  have hb (d : Decision) (b : Bool) : SameWGStore (branch d b) :=
    fun initial => hoare_liftAmbient (AmbientM.branch d b) (fun w => wgStoreView w = initial)
  unfold configureKeepaliveValuePrefix
  simp only [liftWGObserver_bind, liftWGObserver_pure]
  apply PrefixEnsures.bind (c.getPeer P pid)
  intro p
  apply PrefixEnsures.bind (c.nativeStore (fun s => P s ∧ s.1.slots pid = some p.internalId) _
    (andM_sameView (hb _ _) (andM_sameView (hb _ _) (hb _ _))))
  intro send
  exact PrefixEnsures.bind (c.setPeer P pid {p with persistentKeepaliveInterval := interval})
    (fun _ => c.pure P send)

theorem configureKeepalivePrefix_preserves_product (c : ProductAmbientContracts I) (ht : ProductTxContracts I)
    (pid : PeerId) (running : Bool) (interval : Nat) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (configureKeepalivePrefix pid running interval)) := by
  have hb (d : Decision) (b : Bool) : SameWGStore (branch d b) :=
    fun initial => hoare_liftAmbient (AmbientM.branch d b) (fun w => wgStoreView w = initial)
  unfold configureKeepalivePrefix
  simp only [liftWGObserver_bind]
  apply PrefixPreserves.bind (ProductAmbientContracts.drop (configureKeepaliveValuePrefix_spec_product c (fun _ => True) pid running interval))
  intro send
  apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (hb _ _)))
  intro yes
  cases yes
  · simpa only [Bool.false_eq_true, ite_false, liftWGObserver_pure] using PrefixPreserves.pure c.safe ()
  · simpa only [ite_true] using sendKeepalivePrefix_preserves_product c ht pid

structure ProductConfigurationPeerContracts (I : List LifetimeEvent → World → Prop) : Prop where
  nodes : ProductNodeAllocationStable I
  removal : ProductPeerRemovalContracts I
  tx : ProductTxContracts I
  create : ∀ key psk, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (peerCreateMixed key psk))

theorem peerConfigTailPrefix_preserves_product (c : ProductAmbientContracts I) (r : ProductConfigurationPeerContracts I)
    (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (peerConfigTailPrefix a peer pid)) := by
  have hb (d : Decision) (b : Bool) : SameWGStore (branch d b) :=
    fun initial => hoare_liftAmbient (AmbientM.branch d b) (fun w => wgStoreView w = initial)
  change PrefixEnsures _ _ _ _
  unfold peerConfigTailPrefix
  repeat' first
    | (first | rw [liftWGObserver_bind] | rw [liftWGObserver_pure] | rw [liftWGObserver_forIn] | rw [apply_ite])
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head pubkeyLookupPrefix; exact pubkeyLookupPrefix_preserves_product c _)
    | (maintenance_head peerCreateMixed; exact r.create _ _)
    | (maintenance_head peerGetMixed; exact c.peerGet _)
    | (maintenance_head peerRemovePrefix; exact peerRemovePrefix_preserves_product c r.removal _)
    | (maintenance_head modifyPeerKeysPrefix; exact ProductAmbientContracts.drop (modifyPeerKeysPrefix_spec_product c (fun _ => True) _ _ (fun _ => rfl)))
    | (maintenance_head setPeerEndpointPrefix; exact ProductAmbientContracts.drop (setPeerEndpointPrefix_spec_product c (fun _ => True) _ _))
    | (maintenance_head removeByPeerPrefix; exact removeByPeerPrefix_preserves_product c r.removal.allowedIps.nodes _)
    | (maintenance_head setAllowedipPrefix; exact setAllowedipPrefix_preserves_product c r.nodes _ _)
    | (maintenance_head configureKeepalivePrefix; exact configureKeepalivePrefix_preserves_product c r.tx _ _ _)
    | (maintenance_head sendStagedPacketsPrefix; exact sendStagedPacketsPrefix_preserves_product c r.tx _)
    | (maintenance_lift_action_head invariant; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.invariant _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head branch; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (hb _ _)))
    | (maintenance_lift_action_head getDev; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head WG.andM; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (andM_sameView (hb _ _) (hb _ _))))
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
  all_goals try simp_all

theorem peerConfigUpdatePrefix_preserves_product (c : ProductAmbientContracts I) (r : ProductConfigurationPeerContracts I)
    (a : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (peerConfigUpdatePrefix a peer flags psk pid)) := by
  have hb (d : Decision) (b : Bool) : SameWGStore (branch d b) :=
    fun initial => hoare_liftAmbient (AmbientM.branch d b) (fun w => wgStoreView w = initial)
  change PrefixEnsures _ _ _ _
  unfold peerConfigUpdatePrefix
  repeat' first
    | (first | rw [liftWGObserver_bind] | rw [liftWGObserver_pure] | rw [liftWGObserver_forIn] | rw [apply_ite])
    | (maintenance_head peerConfigTailPrefix; exact peerConfigTailPrefix_preserves_product c r _ _ _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head pubkeyLookupPrefix; exact pubkeyLookupPrefix_preserves_product c _)
    | (maintenance_head peerCreateMixed; exact r.create _ _)
    | (maintenance_head peerGetMixed; exact c.peerGet _)
    | (maintenance_head peerRemovePrefix; exact peerRemovePrefix_preserves_product c r.removal _)
    | (maintenance_head modifyPeerKeysPrefix; exact ProductAmbientContracts.drop (modifyPeerKeysPrefix_spec_product c (fun _ => True) _ _ (fun _ => rfl)))
    | (maintenance_head setPeerEndpointPrefix; exact ProductAmbientContracts.drop (setPeerEndpointPrefix_spec_product c (fun _ => True) _ _))
    | (maintenance_head removeByPeerPrefix; exact removeByPeerPrefix_preserves_product c r.removal.allowedIps.nodes _)
    | (maintenance_head setAllowedipPrefix; exact setAllowedipPrefix_preserves_product c r.nodes _ _)
    | (maintenance_head configureKeepalivePrefix; exact configureKeepalivePrefix_preserves_product c r.tx _ _ _)
    | (maintenance_head sendStagedPacketsPrefix; exact sendStagedPacketsPrefix_preserves_product c r.tx _)
    | (maintenance_lift_action_head invariant; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.invariant _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head branch; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (hb _ _)))
    | (maintenance_lift_action_head getDev; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head WG.andM; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (andM_sameView (hb _ _) (hb _ _))))
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
  all_goals try simp_all

theorem setPeerCmdPrefix_preserves_product (c : ProductAmbientContracts I) (r : ProductConfigurationPeerContracts I)
    (a : PeerAttrs) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (setPeerCmdPrefix a)) := by
  have hb (d : Decision) (b : Bool) : SameWGStore (branch d b) :=
    fun initial => hoare_liftAmbient (AmbientM.branch d b) (fun w => wgStoreView w = initial)
  change PrefixEnsures _ _ _ _
  unfold setPeerCmdPrefix
  repeat' first
    | (first | rw [liftWGObserver_bind] | rw [liftWGObserver_pure] | rw [liftWGObserver_forIn] | rw [apply_ite])
    | (maintenance_head peerConfigUpdatePrefix; exact peerConfigUpdatePrefix_preserves_product c r _ _ _ _ _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head pubkeyLookupPrefix; exact pubkeyLookupPrefix_preserves_product c _)
    | (maintenance_head peerCreateMixed; exact r.create _ _)
    | (maintenance_head peerGetMixed; exact c.peerGet _)
    | (maintenance_head peerRemovePrefix; exact peerRemovePrefix_preserves_product c r.removal _)
    | (maintenance_head modifyPeerKeysPrefix; exact ProductAmbientContracts.drop (modifyPeerKeysPrefix_spec_product c (fun _ => True) _ _ (fun _ => rfl)))
    | (maintenance_head setPeerEndpointPrefix; exact ProductAmbientContracts.drop (setPeerEndpointPrefix_spec_product c (fun _ => True) _ _))
    | (maintenance_head removeByPeerPrefix; exact removeByPeerPrefix_preserves_product c r.removal.allowedIps.nodes _)
    | (maintenance_head setAllowedipPrefix; exact setAllowedipPrefix_preserves_product c r.nodes _ _)
    | (maintenance_head configureKeepalivePrefix; exact configureKeepalivePrefix_preserves_product c r.tx _ _ _)
    | (maintenance_head sendStagedPacketsPrefix; exact sendStagedPacketsPrefix_preserves_product c r.tx _)
    | (maintenance_lift_action_head invariant; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.invariant _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head branch; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (hb _ _)))
    | (maintenance_lift_action_head getDev; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head WG.andM; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (andM_sameView (hb _ _) (hb _ _))))
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
  all_goals try simp_all

end Leanux.Proofs.WG.Lifetimes
