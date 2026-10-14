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
  let send ← liftPrefix (WG.andM (branch .peerKeepaliveWasZero (p.persistentKeepaliveInterval == 0))
    (WG.andM (branch .peerKeepaliveNonzero (interval != 0)) (branch .peerKeepaliveRunning running)))
  setPeerMixed pid {p with persistentKeepaliveInterval := interval}
  return send

def configureKeepalivePrefix (pid : PeerId) (running : Bool) (interval : Nat) : MixedM Unit := do
  let send ← configureKeepaliveValuePrefix pid running interval
  if ← liftPrefix (branch .peerSendKeepalive send) then sendKeepalivePrefix pid

def peerConfigTailPrefix (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) : MixedM Int := do
  let out (peer : Option PeerId) (ret : Int) : MixedM Int := do
    peerPutMixed peer
    _ ← liftPrefix (branch .peerZeroPsk a.presharedKey.isSome)
    return ret
  let mut ret : Int := 0
  if ← liftPrefix (branch .peerHasAips a.allowedIps.isSome) then
    for entry in a.allowedIps.getD [] do
      _ ← liftPrefix (branch .peerAipsIter true)
      match entry with
      | .malformed =>
        _ ← liftPrefix (branch .peerAipParseErr true)
        return ← out peer (-EINVAL)
      | .attrs ip =>
        _ ← liftPrefix (branch .peerAipParseErr false)
        ret ← setAllowedipPrefix pid ip
        if ← liftPrefix (branch .peerAipErr (ret < 0)) then return ← out peer ret
    _ ← liftPrefix (branch .peerAipsIter false)
  let running := (← liftPrefix getDev).running
  if ← liftPrefix (branch .peerHasKeepalive a.keepalive.isSome) then
    configureKeepalivePrefix pid running (a.keepalive.getD 0)
  if ← liftPrefix (branch .peerRunning running) then sendStagedPacketsPrefix pid
  out peer ret

def peerConfigUpdatePrefix (a : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) : MixedM Int := do
  let out (peer : Option PeerId) (ret : Int) : MixedM Int := do
    peerPutMixed peer
    _ ← liftPrefix (branch .peerZeroPsk a.presharedKey.isSome)
    return ret
  if ← liftPrefix (branch .peerRemoveMe (flags &&& WGPEER_F_REMOVE_ME != 0)) then
    peerRemovePrefix peer
    return ← out peer 0
  if ← liftPrefix (branch .peerSetPsk psk.isSome) then
    modifyPeerKeysPrefix pid fun p => {p with presharedKey := psk.getD []}
  if ← liftPrefix (branch .peerHasEndpoint a.endpoint.isSome) then
    let some e := a.endpoint | liftPrefix (invariant "unreachable")
    if ← liftPrefix (WG.andM (branch .peerEndpointV4Len (e.len == 16)) (branch .peerEndpointV4Family (e.family == AF_INET))) then
      setPeerEndpointPrefix pid {family := e.family, addr := e.addr, port := e.port}
    else if ← liftPrefix (WG.andM (branch .peerEndpointV6Len (e.len == 28)) (branch .peerEndpointV6Family (e.family == AF_INET6))) then
      setPeerEndpointPrefix pid {family := e.family, addr := e.addr, port := e.port, scope := e.scope, flowinfo := e.flowinfo}
  if ← liftPrefix (branch .peerReplaceAips (flags &&& WGPEER_F_REPLACE_ALLOWEDIPS != 0)) then removeByPeerPrefix pid
  peerConfigTailPrefix a peer pid

def setPeerCmdPrefix (a : PeerAttrs) : MixedM Int := do
  let out (peer : Option PeerId) (ret : Int) : MixedM Int := do
    peerPutMixed peer
    _ ← liftPrefix (branch .peerZeroPsk a.presharedKey.isSome)
    return ret
  if !(← liftPrefix (WG.andM (branch .peerHasPubkey a.publicKey.isSome) (branch .peerPubkeyLen true))) then
    return ← out none (-EINVAL)
  let some publicKey := a.publicKey | liftPrefix (invariant "unreachable")
  let psk ← do
    if ← liftPrefix (WG.andM (branch .peerHasPsk a.presharedKey.isSome) (branch .peerPskLen true)) then pure a.presharedKey
    else pure none
  let mut flags : UInt32 := 0
  if ← liftPrefix (branch .peerHasFlags a.flags.isSome) then flags := a.flags.getD 0
  if ← liftPrefix (branch .peerBadFlags (flags &&& ~~~WGPEER_F_ALL != 0)) then return ← out none (-EOPNOTSUPP)
  if ← liftPrefix (branch .peerHasProtocol a.protocolVersion.isSome) then
    if ← liftPrefix (branch .peerBadProtocol (a.protocolVersion != some 1)) then return ← out none (-EPFNOSUPPORT)
  let mut peer ← pubkeyLookupPrefix publicKey
  if ← liftPrefix (branch .peerNotFound peer.isNone) then
    if ← liftPrefix (branch .peerNewRemoveOrUpdate (flags &&& (WGPEER_F_REMOVE_ME ||| WGPEER_F_UPDATE_ONLY) != 0)) then
      return ← out none 0
    flags := flags &&& ~~~WGPEER_F_REPLACE_ALLOWEDIPS
    let id := (← liftPrefix getDev).staticIdentity
    if ← liftPrefix (WG.andM (branch .peerSelfHasIdentity id.hasIdentity) (branch .peerSelfKeyMatch (publicKey == id.staticPublic))) then
      return ← out none 0
    match ← peerCreateMixed publicKey psk with
    | .error e =>
      _ ← liftPrefix (branch .peerCreateErr true)
      return ← out none e
    | .ok pid =>
      _ ← liftPrefix (branch .peerCreateErr false)
      peerGetMixed pid
      peer := some pid
  let some pid := peer | liftPrefix (invariant "set_peer without a peer")
  peerConfigUpdatePrefix a peer flags psk pid

theorem peerConfigTailPrefix_erases (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    ErasesPrefix (peerConfigTailPrefix a peer pid) (peerConfigTailSource a peer pid) := by
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
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals simp_all
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
      | with_reducible exact erasesPrefix_lift _
      | with_reducible exact erasesPrefix_pure _
      | with_reducible apply erasesPrefix_forIn
      | with_reducible apply erasesPrefix_bind
      | with_reducible apply erasesPrefix_ite
      | (with_reducible intro x; try dsimp only)
      | (with_reducible split)

theorem peerConfigUpdatePrefix_erases (a : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    ErasesPrefix (peerConfigUpdatePrefix a peer flags psk pid) (peerConfigUpdateSource a peer flags psk pid) := by
  unfold peerConfigUpdatePrefix peerConfigUpdateSource modifyPeerKeysPrefix
  simp only [bind_assoc, pure_bind]
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
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals simp_all
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
      | with_reducible exact erasesPrefix_lift _
      | with_reducible exact erasesPrefix_pure _
      | with_reducible apply erasesPrefix_forIn
      | with_reducible apply erasesPrefix_bind
      | with_reducible apply erasesPrefix_ite
      | (with_reducible intro x; try dsimp only)
      | (with_reducible split)

theorem setPeerCmdPrefix_erases (a : PeerAttrs) : ErasesPrefix (setPeerCmdPrefix a) (setPeerCmd a) := by
  rw [← setPeerCmd_source]
  unfold setPeerCmdPrefix setPeerCmdSource
  simp only [bind_assoc, pure_bind]
  repeat' first
    | with_reducible exact peerConfigUpdatePrefix_erases _ _ _ _ _
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
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals simp_all
  all_goals try simp only [map_eq_pure_bind]
  all_goals
    repeat' first
      | with_reducible exact peerConfigUpdatePrefix_erases _ _ _ _ _
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
      | with_reducible exact erasesPrefix_lift _
      | with_reducible exact erasesPrefix_pure _
      | with_reducible apply erasesPrefix_forIn
      | with_reducible apply erasesPrefix_bind
      | with_reducible apply erasesPrefix_ite
      | (with_reducible intro x; try dsimp only)
      | (with_reducible split)

theorem configureKeepaliveValuePrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (pid : PeerId) (running : Bool) (interval : Nat) :
    AmbientSpec I P (configureKeepaliveValuePrefix pid running interval) (fun _ => P) := by
  unfold configureKeepaliveValuePrefix
  apply PrefixEnsures.bind (c.getPeer P pid)
  intro p
  apply PrefixEnsures.bind (c.kernel (fun s => P s ∧ s.1.slots pid = some p.internalId) _
    (andM_sameKernel (sameKernel_branch _ _) (andM_sameKernel (sameKernel_branch _ _) (sameKernel_branch _ _))))
  intro send
  exact PrefixEnsures.bind (c.setPeer P pid {p with persistentKeepaliveInterval := interval})
    (fun _ => c.pure P send)

theorem configureKeepalivePrefix_preserves (c : AmbientContracts I) (ht : TxContracts I)
    (pid : PeerId) (running : Bool) (interval : Nat) :
    PrefixPreserves I LifetimeEvent.Safe (configureKeepalivePrefix pid running interval) := by
  unfold configureKeepalivePrefix
  apply PrefixPreserves.bind (AmbientContracts.drop (configureKeepaliveValuePrefix_spec c (fun _ => True) pid running interval))
  intro send
  apply PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
  intro yes
  split
  · exact sendKeepalivePrefix_preserves_ambient c ht pid
  · exact PrefixPreserves.pure c.safe ()

structure ConfigurationPeerContracts (I : List LifetimeEvent → World → Prop) : Prop where
  nodes : NodeAllocationStable I
  removal : PeerRemovalContracts I
  tx : TxContracts I
  create : ∀ key psk, PrefixPreserves I LifetimeEvent.Safe (peerCreateMixed key psk)

theorem allocationConfigurationPeer : ConfigurationPeerContracts AllocationInv :=
  ⟨allocationNodeAllocationStable, allocationPeerRemoval, allocationTx, peerCreateMixed_preserves⟩

theorem peerConfigTailPrefix_preserves (c : AmbientContracts I) (r : ConfigurationPeerContracts I)
    (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    PrefixPreserves I LifetimeEvent.Safe (peerConfigTailPrefix a peer pid) := by
  unfold peerConfigTailPrefix
  repeat' first
    | with_reducible exact c.peerPut _
    | with_reducible exact pubkeyLookupPrefix_preserves_ambient c _
    | with_reducible exact r.create _ _
    | with_reducible exact c.peerGet _
    | with_reducible exact peerRemovePrefix_preserves c r.removal _
    | with_reducible exact AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) _ _ (fun _ => rfl))
    | with_reducible exact AmbientContracts.drop (setPeerEndpointPrefix_spec c (fun _ => True) _ _)
    | with_reducible exact removeByPeerPrefix_preserves c r.removal.allowedIps.nodes _
    | with_reducible exact setAllowedipPrefix_preserves c r.nodes _ _
    | with_reducible exact configureKeepalivePrefix_preserves c r.tx _ _ _
    | with_reducible exact sendStagedPacketsPrefix_preserves_ambient c r.tx _
    | with_reducible exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply AmbientContracts.drop (c.kernel (fun _ => True) _ ?_)
    | with_reducible exact sameKernel_branch _ _
    | with_reducible exact getDev_sameKernel
    | with_reducible apply andM_sameKernel
    | with_reducible apply PrefixPreserves.forIn _ _ _ c.safe
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals simp_all

theorem peerConfigUpdatePrefix_preserves (c : AmbientContracts I) (r : ConfigurationPeerContracts I)
    (a : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    PrefixPreserves I LifetimeEvent.Safe (peerConfigUpdatePrefix a peer flags psk pid) := by
  unfold peerConfigUpdatePrefix
  repeat' first
    | with_reducible exact peerConfigTailPrefix_preserves c r _ _ _
    | with_reducible exact c.peerPut _
    | with_reducible exact pubkeyLookupPrefix_preserves_ambient c _
    | with_reducible exact r.create _ _
    | with_reducible exact c.peerGet _
    | with_reducible exact peerRemovePrefix_preserves c r.removal _
    | with_reducible exact AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) _ _ (fun _ => rfl))
    | with_reducible exact AmbientContracts.drop (setPeerEndpointPrefix_spec c (fun _ => True) _ _)
    | with_reducible exact removeByPeerPrefix_preserves c r.removal.allowedIps.nodes _
    | with_reducible exact setAllowedipPrefix_preserves c r.nodes _ _
    | with_reducible exact configureKeepalivePrefix_preserves c r.tx _ _ _
    | with_reducible exact sendStagedPacketsPrefix_preserves_ambient c r.tx _
    | with_reducible exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply AmbientContracts.drop (c.kernel (fun _ => True) _ ?_)
    | with_reducible exact sameKernel_branch _ _
    | with_reducible exact getDev_sameKernel
    | with_reducible apply andM_sameKernel
    | with_reducible apply PrefixPreserves.forIn _ _ _ c.safe
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals simp_all

theorem setPeerCmdPrefix_preserves (c : AmbientContracts I) (r : ConfigurationPeerContracts I)
    (a : PeerAttrs) : PrefixPreserves I LifetimeEvent.Safe (setPeerCmdPrefix a) := by
  unfold setPeerCmdPrefix
  repeat' first
    | with_reducible exact peerConfigUpdatePrefix_preserves c r _ _ _ _ _
    | with_reducible exact c.peerPut _
    | with_reducible exact pubkeyLookupPrefix_preserves_ambient c _
    | with_reducible exact r.create _ _
    | with_reducible exact c.peerGet _
    | with_reducible exact peerRemovePrefix_preserves c r.removal _
    | with_reducible exact AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) _ _ (fun _ => rfl))
    | with_reducible exact AmbientContracts.drop (setPeerEndpointPrefix_spec c (fun _ => True) _ _)
    | with_reducible exact removeByPeerPrefix_preserves c r.removal.allowedIps.nodes _
    | with_reducible exact setAllowedipPrefix_preserves c r.nodes _ _
    | with_reducible exact configureKeepalivePrefix_preserves c r.tx _ _ _
    | with_reducible exact sendStagedPacketsPrefix_preserves_ambient c r.tx _
    | with_reducible exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply AmbientContracts.drop (c.kernel (fun _ => True) _ ?_)
    | with_reducible exact sameKernel_branch _ _
    | with_reducible exact getDev_sameKernel
    | with_reducible apply andM_sameKernel
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

namespace ConfigurationCall

def original : ConfigurationCall → M Int
  | .port p => setPort p
  | .allowedIp pid attrs => setAllowedip pid attrs
  | .peer attrs => setPeerCmd attrs

def observed : ConfigurationCall → MixedM Int
  | .port p => setPortPrefix p
  | .allowedIp pid attrs => setAllowedipPrefix pid attrs
  | .peer attrs => setPeerCmdPrefix attrs

theorem erases (call : ConfigurationCall) : ErasesPrefix call.observed call.original := by
  cases call with
  | port port => exact setPortPrefix_erases port
  | allowedIp pid attrs => exact setAllowedipPrefix_erases pid attrs
  | peer attrs => exact setPeerCmdPrefix_erases attrs

theorem preserves_ambient (c : AmbientContracts I) (hs : SocketControlStable I)
    (r : ConfigurationPeerContracts I) (call : ConfigurationCall) :
    PrefixPreserves I LifetimeEvent.Safe call.observed := by
  cases call with
  | port port => exact setPortPrefix_preserves c hs port
  | allowedIp pid attrs => exact setAllowedipPrefix_preserves c r.nodes pid attrs
  | peer attrs => exact setPeerCmdPrefix_preserves c r attrs

theorem allocation (call : ConfigurationCall) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe call.observed :=
  call.preserves_ambient allocationAmbient allocationSocketControlStable allocationConfigurationPeer

end ConfigurationCall
end Leanux.Proofs.WG.Lifetimes
