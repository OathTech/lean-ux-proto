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
  apply (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  cases hr
  simp [routingView, modifyDev, Option.map_map, Function.comp_def, hf]

/-- Exact normal creation effects on the routing projection, including both
original refusal arms. Initializer record failures have no returned WG/Ambient endpoint. -/
theorem peerCreate_routing_spec (start : WGWorld) (key : Key) (psk : Option Key) :
    ⦃fun w => ⌜wgStoreView w = wgStoreView start⌝⦄ peerCreate key psk
    ⦃⇓? result w => ⌜match result with
      | .error err => err = -ENOMEM ∧ routingView w = routingView start
      | .ok pid => ∃ s, routingView start = some s ∧ pid = s.peerFrontier ∧
          routingView w = some s.allocate⌝⦄ := by
  have ha :
      ⦃fun w => ⌜wgStoreView w = wgStoreView start⌝⦄
        (hiddenAlloc .kmemCacheZallocPeer : WG.M Bool)
      ⦃⇓? _ w => ⌜wgStoreView w = wgStoreView start⌝⦄ :=
    hoare_liftAmbient (AmbientM.hiddenAlloc .kmemCacheZallocPeer)
      (fun w => wgStoreView w = wgStoreView start)
  have hd := fun pid => (dstCacheReset_routing pid).wp
    (fun s => s = (routingView start).map RoutingState.allocate)
  have hh := fun pid => (handshakeInit_routing pid psk).wp
    (fun s => s = (routingView start).map RoutingState.allocate)
  have ht := fun pid => (resetLastSentHandshake_routing pid).wp
    (fun s => s = (routingView start).map RoutingState.allocate)
  mvcgen [peerCreate, ha, hd, hh, ht, getDev, setPeer, modifyDev,
    branch, branchCmp, AmbientM.branch, AmbientM.branchCmp, invariant, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all only [routingView, wgStoreView, WGStoreView.mk.injEq, Option.map_some]
  all_goals obtain ⟨hdev, _⟩ := ‹some _ = start.dev ∧ _›
  all_goals simp only [← hdev, Option.map_some] at *
  all_goals clear hdev
  all_goals try simp_all [routingView, routingState, RoutingState.allocate,
    Std.TreeMap.getElem?_insert, Std.LawfulEqOrd.compare_eq_iff_eq]
  all_goals first | assumption | (funext q; split <;> simp_all [eq_comm])

theorem peerCreate_routing (w v : WGWorld) (ambient ambient' : Ambient) (key : Key) (psk : Option Key)
    (result : Except Int PeerId) (hr : ((peerCreate key psk).run w).run ambient = .ok ((result, v), ambient')) :
    match result with
    | .error err => err = -ENOMEM ∧ routingView v = routingView w
    | .ok pid => ∃ s, routingView w = some s ∧ pid = s.peerFrontier ∧
        routingView v = some s.allocate := by
  have he := (hoare_iff_run_ambient _ _ _).mp (peerCreate_routing_spec w key psk) w ambient result v ambient' rfl hr
  cases result <;> exact he

theorem peerCreate_routing_preserved (w v : WGWorld) (ambient ambient' : Ambient) (d : Device)
    (hd : w.dev = some d) (hi : RoutingInvariant d t4 t6)
    (key : Key) (psk : Option Key) (result : Except Int PeerId)
    (hr : ((peerCreate key psk).run w).run ambient = .ok ((result, v), ambient')) :
    ∃ out, v.dev = some out ∧ RoutingInvariant out t4 t6 := by
  have he := peerCreate_routing w v ambient ambient' key psk result hr
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
theorem peerPut_routing_spec (start : WGWorld) (peer : Option PeerId) :
    ⦃fun w => ⌜wgStoreView w = wgStoreView start⌝⦄ peerPut peer
    ⦃⇓? _ w => ⌜routingView w = routingView start ∨
      ∃ pid, routingView w = (routingView start).map (fun s => s.erase pid)⌝⦄ := by
  have hi (pid : PeerId) :
      ⦃fun w => ⌜routingView w = routingView start⌝⦄
        (MonadLift.monadLift (indexRemove (.handshake pid)) : WG.M Unit)
      ⦃⇓? _ w => ⌜routingView w = routingView start⌝⦄ := by
    apply hoare_liftIndex _ (fun w => routingView w = routingView start)
    intro g d table hg hd
    simpa [routingView, hd, routingState] using hg
  cases peer with
  | none =>
    mvcgen [peerPut, branch, AmbientM.branch]
    simp_all [routingView, wgStoreView]
  | some pid =>
    simp only [peerPut, Option.isNone_some, Option.getD_some, Bool.false_eq_true, ↓reduceIte]
    mvcgen [hi, getPeer, getDev, setPeer, modifyDev,
      requireNotPending, refcountDecAndTest, branch, branchCmp, branchCmpExcluded,
      AmbientM.branch, AmbientM.branchCmp, AmbientM.branchCmpExcluded,
      retirePeerUnits, modifyAmbient, invariant, unsupported, AmbientM.invariant, AmbientM.unsupported]
    all_goals try dsimp +zetaDelta only at *
    all_goals try simp_all only [routingView, wgStoreView, WGStoreView.mk.injEq, Option.map_some]
    all_goals obtain ⟨hdev, _⟩ := ‹some _ = start.dev ∧ _›
    all_goals simp only [← hdev, Option.map_some] at *
    all_goals clear hdev
    all_goals try simp_all [routingView, wgStoreView, routingState, RoutingState.erase,
      Std.TreeMap.getElem?_insert, Std.TreeMap.getElem?_erase,
      Std.LawfulEqOrd.compare_eq_iff_eq]
    all_goals try (funext q; split <;> simp_all)
    all_goals try (apply Or.inl; funext q; split <;> simp_all)
    apply Or.inr
    refine ⟨pid, ?_⟩
    obtain ⟨out, hout, hn, ht, hnf, hpf, hl⟩ := ‹∃ a, _›
    refine ⟨out, hout, hn, ht, hnf, hpf, ?_⟩
    funext q
    have hq := congrFun hl q
    split <;> simp_all [eq_comm]

theorem peerPut_routing_preserved (w v : WGWorld) (ambient ambient' : Ambient) (d : Device)
    (hd : w.dev = some d) (hi : RoutingInvariant d t4 t6)
    (peer : Option PeerId) (hr : ((peerPut peer).run w).run ambient = .ok (((), v), ambient')) :
    ∃ out, v.dev = some out ∧ RoutingInvariant out t4 t6 := by
  have he := (hoare_iff_run_ambient _ _ _).mp (peerPut_routing_spec w peer) w ambient () v ambient' rfl hr
  rcases he with he | ⟨pid, he⟩
  · have hview : routingView v = some (routingState d) := he.trans (by simp [routingView, hd])
    obtain ⟨out, hout, hv⟩ := Option.map_eq_some_iff.mp hview
    exact ⟨out, hout, hi.of_routingState hv⟩
  · have hview : routingView v = some ((routingState d).erase pid) := he.trans (by simp [routingView, hd])
    obtain ⟨out, hout, hv⟩ := Option.map_eq_some_iff.mp hview
    exact ⟨out, hout, (hi.erase pid).of_routingState (hv.trans (routingState_erase d pid).symm)⟩

end Leanux.Proofs.WG.AllowedIps
