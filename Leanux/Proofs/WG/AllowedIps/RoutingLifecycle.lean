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
  simp [routingView, Option.map_map, Function.comp_def, hf]

/-- Exact normal creation effects on the routing projection, including both
original refusal arms. Initializer record failures have no returned WG/Ambient endpoint. -/
theorem peerCreate_routing_spec (start : WGWorld) (key : Key) (psk : Option Key) :
    ⦃fun w => ⌜wgStoreView w = wgStoreView start⌝⦄ peerCreate key psk
    ⦃⇓? result w => ⌜match result with
      | .error err => err = -ENOMEM ∧ routingView w = routingView start
      | .ok pid => ∃ s, routingView start = some s ∧ pid = s.peerFrontier ∧
          routingView w = some s.allocate⌝⦄ := by
  let P := fun w : WGWorld => wgStoreView w = wgStoreView start
  let Q := fun (result : Except Int PeerId) (w : WGWorld) => match result with
    | .error err => err = -ENOMEM ∧ routingView w = routingView start
    | .ok pid => ∃ s, routingView start = some s ∧ pid = s.peerFrontier ∧
        routingView w = some s.allocate
  have view_eq (w : WGWorld) (h : P w) : routingView w = routingView start :=
    congrArg (fun k : WGStoreView => k.dev.map routingState) h
  have ambient {α : Type} (a : AmbientM α) (R : WGWorld → Prop) :
      Preserves R (StateT.lift a) := hoare_liftAmbient a R
  have getter : Hoare getDev P (fun d w => P w ∧ w.dev = some d) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient d out ambient' hi hr
    cases hd : w.dev with
    | none =>
      simp [getDev, hd, invariant, AmbientM.invariant] at hr
      cases hr
    | some saved =>
      simp [getDev, hd] at hr
      rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
      exact ⟨hi, hd⟩
  have fail (d : Device) : Hoare (pure (.error (-ENOMEM)) : WG.M (Except Int PeerId))
      (fun w => P w ∧ w.dev = some d) Q := by
    apply hoare_consequence (hoare_pure (Except.error (-ENOMEM) : Except Int PeerId) _)
    · intro _ h; exact h
    · intro result w h
      rcases h with ⟨rfl, h⟩
      exact ⟨rfl, view_eq w h.1⟩
  have core (d : Device) : Hoare (Peers.peerCreateCore d.nextPeer key)
      (fun w => P w ∧ w.dev = some d)
      (fun _ w => routingView start = some (routingState d) ∧
        routingView w = some (routingState d).allocate) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient u out ambient' hi hr
    rw [Peers.peerCreateCore_run] at hr
    cases hr
    refine ⟨(view_eq w hi.1).symm.trans (by simp [routingView, hi.2]), ?_⟩
    simpa only [Peers.creationCoreWorld, hi.2, Option.map_some, routingView] using
      congrArg some (routingState_allocate d (Peers.createdPeer key (w.peerCounter + 1)) rfl)
  let tail (pid : PeerId) : WG.M (Except Int PeerId) := do
    dstCacheReset pid
    handshakeInit pid psk
    resetLastSentHandshake pid
    modifyDev fun d => {d with peerList := d.peerList ++ [pid], peerHashtable := (key, pid) :: d.peerHashtable, numPeers := d.numPeers + 1}
    return .ok pid
  have tail_spec (d : Device) : Hoare (tail d.nextPeer)
      (fun w => routingView start = some (routingState d) ∧
        routingView w = some (routingState d).allocate) Q := by
    let R := fun v => routingView start = some (routingState d) ∧
      v = some (routingState d).allocate
    unfold tail
    apply hoare_bind _ _ ((dstCacheReset_routing d.nextPeer).wp R)
    intro _
    apply hoare_bind _ _ ((handshakeInit_routing d.nextPeer psk).wp R)
    intro _
    apply hoare_bind _ _ ((resetLastSentHandshake_routing d.nextPeer).wp R)
    intro _
    apply hoare_bind _ _ ((modifyDev_routing (fun d' => {d' with
      peerList := d'.peerList ++ [d.nextPeer],
      peerHashtable := (key, d.nextPeer) :: d'.peerHashtable,
      numPeers := d'.numPeers + 1}) (fun _ => rfl)).wp R)
    intro _
    apply hoare_consequence (hoare_pure (Except.ok d.nextPeer : Except Int PeerId) _)
    · intro _ h; exact h
    · intro result w h
      rcases h with ⟨rfl, h⟩
      exact ⟨routingState d, h.1, rfl, h.2⟩
  have source : Peers.peerCreateFactored key psk = (do
    let d ← getDev
    if ← branchCmp .peerCreateMaxPeers (d.numPeers ≥ MAX_PEERS_PER_DEVICE)
        d.numPeers MAX_PEERS_PER_DEVICE then return .error (-ENOMEM)
    if ← branch .peerCreateNoMem !(← hiddenAlloc .kmemCacheZallocPeer) then
      return .error (-ENOMEM)
    if ← branch .peerCreateDstCacheFail false then return .error (-ENOMEM)
    Peers.peerCreateCore d.nextPeer key
    tail d.nextPeer) := by
    simp only [Peers.peerCreateFactored, tail]
  rw [← Peers.peerCreateFactored_eq, source]
  change Hoare _ P Q
  apply hoare_bind _ _ getter
  intro d
  apply hoare_bind _ _ (ambient (AmbientM.branchCmp .peerCreateMaxPeers
    (d.numPeers ≥ MAX_PEERS_PER_DEVICE) d.numPeers MAX_PEERS_PER_DEVICE)
    (fun w => P w ∧ w.dev = some d))
  intro maxPeers
  cases maxPeers with
  | true => exact fail d
  | false =>
    apply hoare_bind _ _ (ambient (AmbientM.hiddenAlloc .kmemCacheZallocPeer)
      (fun w => P w ∧ w.dev = some d))
    intro allocated
    apply hoare_bind _ _ (ambient (AmbientM.branch .peerCreateNoMem !allocated)
      (fun w => P w ∧ w.dev = some d))
    intro noMem
    cases noMem with
    | true => exact fail d
    | false =>
      apply hoare_bind _ _ (ambient (AmbientM.branch .peerCreateDstCacheFail false)
        (fun w => P w ∧ w.dev = some d))
      intro cacheFailed
      cases cacheFailed with
      | true => exact fail d
      | false => exact hoare_bind _ _ (core d) (fun _ => tail_spec d)

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
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result out ambient' initial hr
  have view_eq : routingView w = routingView start :=
    congrArg (fun k : WGStoreView => k.dev.map routingState) initial
  rw [← view_eq]
  cases peer with
  | none =>
    simp [peerPut, branch, AmbientM.branch] at hr
    rcases hr with ⟨rfl, rfl⟩
    exact Or.inl rfl
  | some pid =>
    cases hd : w.dev with
    | none =>
      simp [peerPut, requireNotPending, getPeer, getDev, hd, branch, AmbientM.branch,
        invariant, AmbientM.invariant] at hr
      cases hr
    | some d =>
      cases hp : d.peers[pid]? with
      | none =>
        simp [peerPut, requireNotPending, getPeer, getDev, hd, hp, branch, AmbientM.branch,
          invariant, AmbientM.invariant] at hr
        cases hr
      | some p =>
        have hl (a : IndexM Unit) : (liftM a : WG.M Unit) = liftIndex a := rfl
        by_cases positive : 0 < p.refcount
        · have nonzero : p.refcount ≠ 0 := by omega
          by_cases final : p.refcount = 1
          all_goals
            simp [peerPut, requireNotPending, getPeer, getDev, setPeer, modifyDev,
              refcountDecAndTest, branch, branchCmp, indexRemove_eq, indexUnhash,
              hl, liftIndex_run, retirePeerUnits, modifyAmbient,
              CounterWindow.branch_run, CounterWindow.branchCmp_run,
              hd, hp, positive, nonzero, final,
              StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
              CounterWindow.except_ok_bind, CounterWindow.except_pure,
              invariant, AmbientM.invariant, unsupported, AmbientM.unsupported] at hr
          all_goals repeat' first | split at hr | contradiction
          all_goals rcases hr with ⟨rfl, rfl⟩
          all_goals simp only [routingView, hd, Option.map_some]
          all_goals first
            | exact Or.inl (congrArg some (routingState_insert_same d pid p _ hp rfl))
            | apply Or.inr; refine ⟨pid, ?_⟩
              exact congrArg some ((routingState_erase
                {d with peers := d.peers.insert pid {p with refcount := 0}} pid).trans
                (congrArg (fun state => state.erase pid)
                  (routingState_insert_same d pid p {p with refcount := 0} hp rfl)))
        · have zero : p.refcount = 0 := by omega
          simp [peerPut, requireNotPending, getPeer, getDev, setPeer, modifyDev,
            refcountDecAndTest, branch, branchCmp, CounterWindow.branch_run,
            CounterWindow.branchCmp_run, hd, hp, zero,
            StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
            CounterWindow.except_ok_bind, CounterWindow.except_pure,
            unsupported, AmbientM.unsupported] at hr
          cases hr

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
