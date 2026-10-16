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
  let d ← liftWGPrefix getDev
  if ← liftWGPrefix (branch .setPortSame (d.incomingPort == port)) then return 0
  for pid in d.peerList do
    _ ← liftWGPrefix (branch .setPortPeerIter true)
    clearPeerEndpointSrcPrefix pid
  _ ← liftWGPrefix (branch .setPortPeerIter false)
  if ← liftWGPrefix (branch .setPortNotRunning !d.running) then
    liftWGPrefix (modifyDev fun d => {d with incomingPort := port})
    return 0
  liftWGPrefix (socketInit port)

def setAllowedipPrefix (pid : PeerId) (ip : AllowedIpAttrs) : MixedM Int := do
  if ← liftWGPrefix (WG.orM (branch .aipNoFamily ip.family.isNone)
      (WG.orM (branch .aipNoAddr ip.addr.isNone) (branch .aipNoCidr ip.cidr.isNone))) then
    return -EINVAL
  let family := ip.family.getD 0
  let addr := ip.addr.getD 0
  let cidr := ip.cidr.getD 0
  if ← liftWGPrefix (WG.andM (branch .aipV4Family (family == AF_INET))
      (WG.andM (branch .aipV4Cidr (cidr ≤ 32)) (branch .aipV4Len (ip.addrLen == 4)))) then
    return ← insertAllowedIpPrefix 4 addr cidr pid
  if ← liftWGPrefix (WG.andM (branch .aipV6Family (family == AF_INET6))
      (WG.andM (branch .aipV6Cidr (cidr ≤ 128)) (branch .aipV6Len (ip.addrLen == 16)))) then
    return ← insertAllowedIpPrefix 6 addr cidr pid
  return -EINVAL

theorem setPortPrefix_erases (port : Nat) : ErasesStatePrefix (setPortPrefix port) (setPort port) := by
  unfold setPortPrefix setPort
  repeat' first
    | with_reducible exact clearPeerEndpointSrcPrefix_erases _
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_forIn
    | with_reducible apply erasesStatePrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem setAllowedipPrefix_erases (pid : PeerId) (ip : AllowedIpAttrs) :
    ErasesStatePrefix (setAllowedipPrefix pid ip) (setAllowedip pid ip) := by
  unfold setAllowedipPrefix setAllowedip
  repeat' first
    | with_reducible exact insertAllowedIpPrefix_erases _ _ _ _
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem incomingPort_sameSocket (port : Nat) :
    SameView socketStoreView (modifyDev fun d => {d with incomingPort := port}) := by
  have h : SameSocket (modifyDev fun d => {d with incomingPort := port}) := by
    intro s
    exact modifyDev_socket_spec (fun t => t = s) _ (fun _ => rfl)
  exact h.factor WGOwnedView.toWGStoreView

theorem setPortPrefix_preserves (c : AmbientContracts I) (hs : SocketControlStable I)
    (port : Nat) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (setPortPrefix port) := by
  have branchFrame (d : Decision) (b : Bool) : SameWGStore (branch d b) := by
    intro initial
    exact hoare_liftAmbient (AmbientM.branch d b) (fun w => wgStoreView w = initial)
  change StatePrefixEnsures _ _ _ _
  unfold setPortPrefix
  repeat' first
    | (maintenance_head clearPeerEndpointSrcPrefix; exact AmbientContracts.drop (clearPeerEndpointSrcPrefix_spec c (fun _ => True) _))
    | (maintenance_lift_action_head socketInit; exact socketControlLift_preserves c hs _ ((socketInit_sameSocket _).factor WGOwnedView.toWGStoreView))
    | (maintenance_lift_action_head modifyDev; exact socketControlLift_preserves c hs _ (incomingPort_sameSocket _))
    | (maintenance_lift_action_head branch; exact AmbientContracts.drop (c.store (fun _ => True) _ (branchFrame _ _)))
    | (maintenance_lift_action_head getDev; exact AmbientContracts.drop (c.store (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_head ForIn.forIn; apply StatePrefixEnsures.forInInvariant _ _ _ (fun _ h w _ => I h w) LifetimeEvent.Safe (fun _ h w _ hi => c.safe h w hi); intro x b; change StatePrefixEnsures _ _ _ _)
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem setAllowedipPrefix_preserves (c : AmbientContracts I) (hs : NodeAllocationStable I)
    (pid : PeerId) (ip : AllowedIpAttrs) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (setAllowedipPrefix pid ip) := by
  have branchFrame (d : Decision) (b : Bool) : SameWGStore (branch d b) := by
    intro initial
    exact hoare_liftAmbient (AmbientM.branch d b) (fun w => wgStoreView w = initial)
  change StatePrefixEnsures _ _ _ _
  unfold setAllowedipPrefix
  repeat' first
    | (maintenance_head insertAllowedIpPrefix; exact insertAllowedIpPrefix_preserves c hs _ _ _ _)
    | (maintenance_lift_action_head WG.orM; exact AmbientContracts.drop (c.store (fun _ => True) _ (orM_sameView (branchFrame _ _) (orM_sameView (branchFrame _ _) (branchFrame _ _)))))
    | (maintenance_lift_action_head WG.andM; exact AmbientContracts.drop (c.store (fun _ => True) _ (andM_sameView (branchFrame _ _) (andM_sameView (branchFrame _ _) (branchFrame _ _)))))
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem setPortPrefix_preserves_product (c : ProductAmbientContracts I) (hs : ProductSocketControlStable I)
    (port : Nat) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (setPortPrefix port)) := by
  have branchFrame (d : Decision) (b : Bool) : SameWGStore (branch d b) := by
    intro initial
    exact hoare_liftAmbient (AmbientM.branch d b) (fun w => wgStoreView w = initial)
  change PrefixEnsures _ _ _ _
  unfold setPortPrefix
  repeat' first
    | (first | rw [liftWGObserver_bind] | rw [liftWGObserver_pure] | rw [liftWGObserver_forIn] | rw [apply_ite])
    | (maintenance_head clearPeerEndpointSrcPrefix; exact ProductAmbientContracts.drop (clearPeerEndpointSrcPrefix_spec_product c (fun _ => True) _))
    | (maintenance_lift_action_head socketInit; exact socketControlNative_preserves_product c hs _ ((socketInit_sameSocket _).factor WGOwnedView.toWGStoreView))
    | (maintenance_lift_action_head modifyDev; exact socketControlNative_preserves_product c hs _ (incomingPort_sameSocket _))
    | (maintenance_lift_action_head branch; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (branchFrame _ _)))
    | (maintenance_lift_action_head getDev; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_head ForIn.forIn; apply PrefixPreserves.forIn _ _ _ c.safe; intro x b; change PrefixEnsures _ _ _ _)
    | (maintenance_head Pure.pure; exact PrefixPreserves.pure c.safe _)
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem setAllowedipPrefix_preserves_product (c : ProductAmbientContracts I) (hs : ProductNodeAllocationStable I)
    (pid : PeerId) (ip : AllowedIpAttrs) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (setAllowedipPrefix pid ip)) := by
  have branchFrame (d : Decision) (b : Bool) : SameWGStore (branch d b) := by
    intro initial
    exact hoare_liftAmbient (AmbientM.branch d b) (fun w => wgStoreView w = initial)
  change PrefixEnsures _ _ _ _
  unfold setAllowedipPrefix
  repeat' first
    | (first | rw [liftWGObserver_bind] | rw [liftWGObserver_pure] | rw [liftWGObserver_forIn] | rw [apply_ite])
    | (maintenance_head insertAllowedIpPrefix; exact insertAllowedIpPrefix_preserves_product c hs _ _ _ _)
    | (maintenance_lift_action_head WG.orM; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (orM_sameView (branchFrame _ _) (orM_sameView (branchFrame _ _) (branchFrame _ _)))))
    | (maintenance_lift_action_head WG.andM; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (andM_sameView (branchFrame _ _) (andM_sameView (branchFrame _ _) (branchFrame _ _)))))
    | (maintenance_head Pure.pure; exact PrefixPreserves.pure c.safe _)
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

end Leanux.Proofs.WG.Lifetimes
