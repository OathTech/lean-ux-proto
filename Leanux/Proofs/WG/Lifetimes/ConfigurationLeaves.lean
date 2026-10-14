import Leanux.Proofs.WG.Lifetimes.AllowedIpsInsert
import Leanux.Proofs.WG.Lifetimes.DeviceControls
import Leanux.Proofs.WG.Lifetimes.HandshakeReceive
import Leanux.WG.Netlink

/-! Original port and allowed-IP attribute configuration. The captured peer
list contains scalar IDs; each endpoint-source helper resolves its actual peer.
Attribute predicates and socket initialization have no tracked resident reads.
All short-circuit records, ordinary negative returns and Stops are retained. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def setPortPrefix (port : Nat) : MixedM Int := do
  let d ← liftPrefix getDev
  if ← liftPrefix (branch .setPortSame (d.incomingPort == port)) then return 0
  for pid in d.peerList do
    _ ← liftPrefix (branch .setPortPeerIter true)
    clearPeerEndpointSrcPrefix pid
  _ ← liftPrefix (branch .setPortPeerIter false)
  if ← liftPrefix (branch .setPortNotRunning !d.running) then
    liftPrefix (modifyDev fun d => {d with incomingPort := port})
    return 0
  liftPrefix (socketInit port)

def setAllowedipPrefix (pid : PeerId) (ip : AllowedIpAttrs) : MixedM Int := do
  if ← liftPrefix (WG.orM (branch .aipNoFamily ip.family.isNone)
      (WG.orM (branch .aipNoAddr ip.addr.isNone) (branch .aipNoCidr ip.cidr.isNone))) then
    return -EINVAL
  let family := ip.family.getD 0
  let addr := ip.addr.getD 0
  let cidr := ip.cidr.getD 0
  if ← liftPrefix (WG.andM (branch .aipV4Family (family == AF_INET))
      (WG.andM (branch .aipV4Cidr (cidr ≤ 32)) (branch .aipV4Len (ip.addrLen == 4)))) then
    return ← insertAllowedIpPrefix 4 addr cidr pid
  if ← liftPrefix (WG.andM (branch .aipV6Family (family == AF_INET6))
      (WG.andM (branch .aipV6Cidr (cidr ≤ 128)) (branch .aipV6Len (ip.addrLen == 16)))) then
    return ← insertAllowedIpPrefix 6 addr cidr pid
  return -EINVAL

theorem setPortPrefix_erases (port : Nat) : ErasesPrefix (setPortPrefix port) (setPort port) := by
  unfold setPortPrefix setPort
  repeat' first
    | with_reducible exact clearPeerEndpointSrcPrefix_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem setAllowedipPrefix_erases (pid : PeerId) (ip : AllowedIpAttrs) :
    ErasesPrefix (setAllowedipPrefix pid ip) (setAllowedip pid ip) := by
  unfold setAllowedipPrefix setAllowedip
  repeat' first
    | with_reducible exact insertAllowedIpPrefix_erases _ _ _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem incomingPort_sameSocketKernel (port : Nat) :
    SameSocketKernel (modifyDev fun d => {d with incomingPort := port}) := by
  apply SameView.of_wp
  intro s
  exact modifyDev_socket_spec (fun t => t = s) _ (fun _ => rfl)

theorem setPortPrefix_preserves (c : AmbientContracts I) (hs : SocketControlStable I)
    (port : Nat) : PrefixPreserves I LifetimeEvent.Safe (setPortPrefix port) := by
  unfold setPortPrefix
  repeat' first
    | with_reducible exact AmbientContracts.drop (clearPeerEndpointSrcPrefix_spec c (fun _ => True) _)
    | with_reducible exact socketControlLift_preserves c hs _ (socketInit_sameSocketKernel _)
    | with_reducible exact socketControlLift_preserves c hs _ (incomingPort_sameSocketKernel _)
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ getDev_sameKernel)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.forIn _ _ _ c.safe
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem setAllowedipPrefix_preserves (c : AmbientContracts I) (hn : NodeAllocationStable I)
    (pid : PeerId) (ip : AllowedIpAttrs) :
    PrefixPreserves I LifetimeEvent.Safe (setAllowedipPrefix pid ip) := by
  unfold setAllowedipPrefix
  repeat' first
    | with_reducible exact insertAllowedIpPrefix_preserves c hn _ _ _ _
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply AmbientContracts.drop (c.kernel (fun _ => True) _ ?_)
    | with_reducible exact sameKernel_branch _ _
    | with_reducible apply andM_sameKernel
    | with_reducible apply orM_sameKernel
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

end Leanux.Proofs.WG.Lifetimes
