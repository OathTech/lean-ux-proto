import Leanux.Proofs.WG.AllowedIps.RoutingView
import Leanux.Proofs.WG.AllowedIps.InsertionRouting

/-! Original peer creation and raw release preserve coherent routing. A release
may orphan raw owner labels; the invariant deliberately permits that. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do
set_option maxHeartbeats 1500000
set_option pp.structureInstances false

def RoutingState.allocate (s : RoutingState) : RoutingState :=
  {s with
    peerFrontier := s.peerFrontier + 1
    lists := fun q => if q = s.peerFrontier then some [] else s.lists q}

def RoutingState.erase (s : RoutingState) (pid : Nat) : RoutingState :=
  {s with lists := fun q => if q = pid then none else s.lists q}

theorem routingState_allocate (d : Device) (p : Peer) (hp : p.allowedipsList = []) :
    routingState {d with nextPeer := d.nextPeer + 1, peers := d.peers.insert d.nextPeer p} =
      (routingState d).allocate := by
  unfold routingState RoutingState.allocate
  congr 1
  funext q
  simp only [Std.TreeMap.getElem?_insert, Std.LawfulEqOrd.compare_eq_iff_eq]
  by_cases hq : d.nextPeer = q <;> simp_all [eq_comm]

theorem routingState_erase (d : Device) (pid : Nat) :
    routingState {d with peers := d.peers.erase pid} = (routingState d).erase pid := by
  unfold routingState RoutingState.erase
  congr 1
  funext q
  simp only [Std.TreeMap.getElem?_erase, Std.LawfulEqOrd.compare_eq_iff_eq]
  by_cases hq : pid = q <;> simp_all [eq_comm]

theorem RoutingInvariant.allocate (hi : RoutingInvariant d t4 t6)
    (p : Peer) (hp : p.allowedipsList = []) :
    RoutingInvariant {d with nextPeer := d.nextPeer + 1, peers := d.peers.insert d.nextPeer p} t4 t6 := by
  refine ⟨hi.forest, hi.valid4, hi.valid6, hi.compressed4, hi.compressed6,
    hi.nodup4, hi.nodup6, hi.below, ?_, ?_, ?_⟩
  · intro q old hq
    simp only [Std.TreeMap.getElem?_insert] at hq
    split at hq
    · rename_i he
      have heq : d.nextPeer = q := by simpa using he
      subst q
      cases hq
      rw [hp]
      refine ⟨by simp, ?_⟩
      intro id
      simp only [List.not_mem_nil, false_iff]
      rintro ⟨e, he, _, ho⟩
      have hb := hi.owners e he
      omega
    · exact hi.lists q old hq
  · intro e he
    exact Nat.lt_succ_of_lt (hi.owners e he)
  · intro q old hq
    simp only [Std.TreeMap.getElem?_insert] at hq
    split at hq
    · rename_i he
      have heq : d.nextPeer = q := by simpa using he
      subst q
      exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (hi.peerSlots q old hq)

theorem RoutingInvariant.erase (hi : RoutingInvariant d t4 t6) (pid : Nat) :
    RoutingInvariant {d with peers := d.peers.erase pid} t4 t6 := by
  refine ⟨hi.forest, hi.valid4, hi.valid6, hi.compressed4, hi.compressed6,
    hi.nodup4, hi.nodup6, hi.below, ?_, hi.owners, ?_⟩
  · intro q old hq
    simp only [Std.TreeMap.getElem?_erase] at hq
    split at hq
    · contradiction
    · exact hi.lists q old hq
  · intro q old hq
    simp only [Std.TreeMap.getElem?_erase] at hq
    split at hq
    · contradiction
    · exact hi.peerSlots q old hq

theorem modifyDev_routing (f : Device → Device)
    (hf : ∀ d, routingState (f d) = routingState d) : SameView routingView (modifyDev f) := by
  intro w x v hr
  cases hr
  simp [routingView, modifyDev, modifyK, Option.map_map, Function.comp_def, hf]

theorem indexRemove_routing (pid : PeerId) (kind : IndexKind) :
    SameView routingView (indexRemove pid kind) := by
  apply (indexRemove_sameIndexKernel pid kind).of_factor
    (fun k : Kernel => k.wg.map routingState) routingView
  intro w
  simp [routingView, indexKernelView, indexKernel, routingState, Option.map_map, Function.comp_def]
  rfl

/-- Exact normal creation effects on the routing projection, including both
original refusal arms. Initializer record failures have no returned World. -/
theorem peerCreate_routing_spec (start : World) (key : Key) (psk : Option Key) :
    ⦃fun w => ⌜w.k = start.k⌝⦄ peerCreate key psk
    ⦃⇓? result w => ⌜match result with
      | .error err => err = -ENOMEM ∧ routingView w = routingView start
      | .ok pid => ∃ s, routingView start = some s ∧ pid = s.peerFrontier ∧
          routingView w = some s.allocate⌝⦄ := by
  have ha := sameKernel_wp _ (hiddenAlloc_sameKernel .kmemCacheZallocPeer) (fun k => k = start.k)
  have hd := fun pid => (dstCacheReset_routing pid).wp
    (fun s => s = (routingView start).map RoutingState.allocate)
  have hh := fun pid => (handshakeInit_routing pid psk).wp
    (fun s => s = (routingView start).map RoutingState.allocate)
  have ht := fun pid => (resetLastSentHandshake_routing pid).wp
    (fun s => s = (routingView start).map RoutingState.allocate)
  mvcgen [peerCreate, ha, hd, hh, ht, getDev, getK, setPeer, modifyDev, modifyK,
    branch, branchCmp, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all only [routingView, Option.map_some]
  all_goals try exact routingState_allocate _ _ rfl
  all_goals try simp_all [routingView, routingState, RoutingState.allocate,
    Std.TreeMap.getElem?_insert, Std.LawfulEqOrd.compare_eq_iff_eq]
  all_goals first | assumption | (funext q; split <;> simp_all [eq_comm])

theorem peerCreate_routing (w v : World) (key : Key) (psk : Option Key)
    (result : Except Int PeerId) (hr : (peerCreate key psk).run w = .ok (result, v)) :
    match result with
    | .error err => err = -ENOMEM ∧ routingView v = routingView w
    | .ok pid => ∃ s, routingView w = some s ∧ pid = s.peerFrontier ∧
        routingView v = some s.allocate := by
  have he := (hoare_iff_triple _ _ _).mpr (peerCreate_routing_spec w key psk) w result v rfl hr
  cases result <;> exact he

theorem peerCreate_routing_preserved (w v : World) (d : Device)
    (hd : w.k.wg = some d) (hi : RoutingInvariant d t4 t6)
    (key : Key) (psk : Option Key) (result : Except Int PeerId)
    (hr : (peerCreate key psk).run w = .ok (result, v)) :
    ∃ out, v.k.wg = some out ∧ RoutingInvariant out t4 t6 := by
  have he := peerCreate_routing w v key psk result hr
  cases result with
  | error err =>
    have hview : routingView v = some (routingState d) := he.2.trans (by simp [routingView, hd])
    obtain ⟨out, hout, hv⟩ := Option.map_eq_some_iff.mp hview
    exact ⟨out, hout, hi.of_routingState hv⟩
  | ok pid =>
    obtain ⟨s, hs, _, he⟩ := he
    have hstate : s = routingState d := by simpa [routingView, hd] using hs.symm
    subst s
    obtain ⟨out, hout, hv⟩ := Option.map_eq_some_iff.mp he
    let p : Peer := Peers.createdPeer [] 0
    have hp : p.allowedipsList = [] := rfl
    exact ⟨out, hout, (hi.allocate p hp).of_routingState
      (hv.trans (routingState_allocate d p hp).symm)⟩

/-- Normal release either retains the routing projection or deletes one peer
list. It leaves the represented prefixes intact, even if their owner vanishes. -/
theorem peerPut_routing_spec (start : World) (peer : Option PeerId) :
    ⦃fun w => ⌜w.k = start.k⌝⦄ peerPut peer
    ⦃⇓? _ w => ⌜routingView w = routingView start ∨
      ∃ pid, routingView w = (routingView start).map (fun s => s.erase pid)⌝⦄ := by
  have hi := fun pid => (indexRemove_routing pid .handshake).wp
    (fun s => s = routingView start)
  simp only [peerPut]
  mvcgen [hi, getPeer, getDev, getK, setPeer, modifyDev, modifyK,
    requireNotPending, refcountDecAndTest, branch, branchCmp, branchCmpExcluded,
    retirePeerUnits, invariant, unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all only [routingView, Option.map_some]
  all_goals try simp_all [routingView, routingState, RoutingState.erase,
    Std.TreeMap.getElem?_insert, Std.TreeMap.getElem?_erase,
    Std.LawfulEqOrd.compare_eq_iff_eq]
  all_goals try (funext q; split <;> simp_all)
  all_goals try (apply Or.inl; funext q; split <;> simp_all)
  apply Or.inr
  refine ⟨peer.getD 0, ?_⟩
  obtain ⟨out, hout, hn, ht, hnf, hpf, hl⟩ := ‹∃ a, _›
  refine ⟨out, hout, hn, ht, hnf, hpf, ?_⟩
  funext q
  have hq := congrFun hl q
  split <;> simp_all [eq_comm]

theorem peerPut_routing_preserved (w v : World) (d : Device)
    (hd : w.k.wg = some d) (hi : RoutingInvariant d t4 t6)
    (peer : Option PeerId) (hr : (peerPut peer).run w = .ok ((), v)) :
    ∃ out, v.k.wg = some out ∧ RoutingInvariant out t4 t6 := by
  have he := (hoare_iff_triple _ _ _).mpr (peerPut_routing_spec w peer) w () v rfl hr
  rcases he with he | ⟨pid, he⟩
  · have hview : routingView v = some (routingState d) := he.trans (by simp [routingView, hd])
    obtain ⟨out, hout, hv⟩ := Option.map_eq_some_iff.mp hview
    exact ⟨out, hout, hi.of_routingState hv⟩
  · have hview : routingView v = some ((routingState d).erase pid) := he.trans (by simp [routingView, hd])
    obtain ⟨out, hout, hv⟩ := Option.map_eq_some_iff.mp hview
    exact ⟨out, hout, (hi.erase pid).of_routingState (hv.trans (routingState_erase d pid).symm)⟩

end Leanux.Proofs.WG.AllowedIps
