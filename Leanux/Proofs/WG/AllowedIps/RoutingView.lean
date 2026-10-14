import Leanux.Proofs.WG.AllowedIps.RoutingInvariant
import Leanux.Proofs.WG.Peers.CreationAccess
import Leanux.Proofs.Framing.PeerBorrow

/-! The routing projection retains device absence and resident peer-list
absence. Other peer fields are irrelevant to the trie invariant. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

structure RoutingState where
  nodes : Std.TreeMap Nat AipNode
  table : AllowedIps
  nodeFrontier : Nat
  peerFrontier : Nat
  lists : PeerId → Option (List NodeId)

def routingState (d : Device) : RoutingState :=
  ⟨d.nodes, d.peerAllowedips, d.nextNode, d.nextPeer,
    fun pid => d.peers[pid]?.map (·.allowedipsList)⟩

def routingView (w : World) : Option RoutingState := w.k.wg.map routingState

theorem RoutingInvariant.of_routingState (hi : RoutingInvariant d t4 t6)
    (he : routingState out = routingState d) : RoutingInvariant out t4 t6 := by
  have hn := congrArg RoutingState.nodes he
  have ht := congrArg RoutingState.table he
  have hnf := congrArg RoutingState.nodeFrontier he
  have hpf := congrArg RoutingState.peerFrontier he
  have hl := congrArg RoutingState.lists he
  change out.nodes = d.nodes at hn
  change out.peerAllowedips = d.peerAllowedips at ht
  change out.nextNode = d.nextNode at hnf
  change out.nextPeer = d.nextPeer at hpf
  refine ⟨?_, hi.valid4, hi.valid6, hi.compressed4, hi.compressed6,
    hi.nodup4, hi.nodup6, ?_, ?_, ?_, ?_⟩
  · simpa only [ForestRep, hn, ht] using hi.forest
  · simpa only [NodesBelow, hn, hnf] using hi.below
  · intro pid p hp
    have hh := congrFun hl pid
    change out.peers[pid]?.map (·.allowedipsList) = d.peers[pid]?.map (·.allowedipsList) at hh
    rw [hp] at hh
    obtain ⟨old, hold, hlist⟩ := Option.map_eq_some_iff.mp hh.symm
    simpa only [hlist] using hi.lists pid old hold
  · simpa only [OwnersBelow, hpf] using hi.owners
  · intro pid p hp
    have hh := congrFun hl pid
    change out.peers[pid]?.map (·.allowedipsList) = d.peers[pid]?.map (·.allowedipsList) at hh
    rw [hp] at hh
    obtain ⟨old, hold, _⟩ := Option.map_eq_some_iff.mp hh.symm
    rw [hpf]
    exact hi.peerSlots pid old hold

theorem routingState_insert_same (d : Device) (pid : PeerId) (old p : Peer)
    (hp : d.peers[pid]? = some old) (hl : p.allowedipsList = old.allowedipsList) :
    routingState {d with peers := d.peers.insert pid p} = routingState d := by
  unfold routingState
  congr 1
  funext q
  by_cases hq : pid = q
  · subst q; simp [hp, hl]
  · simp [Std.TreeMap.getElem?_insert, hq]

theorem routing_getPeer (P : Option RoutingState → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (routingView w)⌝⦄ getPeer pid
    ⦃⇓? p w => ⌜P (routingView w) ∧
      (w.k.wg.bind fun d => d.peers[pid]?.map (·.allowedipsList)) = some p.allowedipsList⌝⦄ := by
  mvcgen [getPeer, getDev, getK, invariant]
  all_goals simp_all

theorem routing_setPeer (P : Option RoutingState → Prop) (pid : PeerId) (p : Peer) :
    ⦃fun w => ⌜P (routingView w) ∧
      (w.k.wg.bind fun d => d.peers[pid]?.map (·.allowedipsList)) = some p.allowedipsList⌝⦄ setPeer pid p
    ⦃⇓? _ w => ⌜P (routingView w)⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v hi hr
  cases x
  cases hd : w.k.wg with
  | none => simp [hd] at hi
  | some d =>
    obtain ⟨old, hold, hl⟩ := Option.map_eq_some_iff.mp (by simpa [hd] using hi.2)
    have he := routingState_insert_same d pid old p hold hl.symm
    cases hr
    simpa [routingView, setPeer, modifyDev, modifyK, hd, he] using hi.1

theorem routing_kernel (a : M α) (ha : SameKernel a) : SameView routingView a :=
  fun w x v hr => congrArg (fun k : Kernel => k.wg.map routingState) (ha w x v hr)

theorem dstCacheReset_routing (pid : PeerId) : SameView routingView (dstCacheReset pid) := by
  apply SameView.of_wp
  intro s
  have hg := routing_getPeer (fun t => t = s)
  have hs := routing_setPeer (fun t => t = s)
  have ht := (routing_kernel _ (hiddenJiffies_sameKernel .dstCacheResetTs)).wp (fun t => t = s)
  mvcgen [dstCacheReset, hg, hs, ht]
  all_goals simp_all

theorem resetLastSentHandshake_routing (pid : PeerId) : SameView routingView (resetLastSentHandshake pid) := by
  apply SameView.of_wp
  intro s
  have hg := routing_getPeer (fun t => t = s)
  have hs := routing_setPeer (fun t => t = s)
  have ht := (routing_kernel _ (hiddenClock64_sameKernel .resetLastSent)).wp (fun t => t = s)
  mvcgen [resetLastSentHandshake, hg, hs, ht]
  all_goals simp_all

theorem precomputeStaticStatic_routing (pid : PeerId) : SameView routingView (precomputeStaticStatic pid) := by
  apply SameView.of_wp
  intro s
  have hg := routing_getPeer (fun t => t = s)
  have hs := routing_setPeer (fun t => t = s)
  mvcgen [precomputeStaticStatic, requireNotPending, hg, hs, getDev, getK, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [routingView]

theorem handshakeInit_routing (pid : PeerId) (psk : Option Key) : SameView routingView (handshakeInit pid psk) := by
  apply SameView.of_wp
  intro s
  have hg := routing_getPeer (fun t => t = s)
  have hs := routing_setPeer (fun t => t = s)
  have ht := (precomputeStaticStatic_routing pid).wp (fun t => t = s)
  mvcgen [handshakeInit, hg, hs, ht, branch]
  all_goals simp_all

end Leanux.Proofs.WG.AllowedIps
