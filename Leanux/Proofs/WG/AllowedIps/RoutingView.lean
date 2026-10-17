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

def routingView (w : WGWorld) : Option RoutingState := w.dev.map routingState

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
      (w.dev.bind fun d => d.peers[pid]?.map (·.allowedipsList)) = some p.allowedipsList⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient p v ambient' h run
  cases hd : w.dev with
  | none =>
    simp [getPeer, getDev, hd, invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    cases hp : d.peers[pid]? with
    | none =>
      simp [getPeer, getDev, hd, hp, invariant, AmbientM.invariant] at run
      cases run
    | some old =>
      have exactRun : ((getPeer pid).run w).run ambient = .ok ((old, w), ambient) := by
        simp [getPeer, getDev, hd, hp] <;> rfl
      rw [exactRun] at run
      cases run
      exact ⟨h, by simp [hd, hp]⟩

theorem routing_setPeer (P : Option RoutingState → Prop) (pid : PeerId) (p : Peer) :
    ⦃fun w => ⌜P (routingView w) ∧
      (w.dev.bind fun d => d.peers[pid]?.map (·.allowedipsList)) = some p.allowedipsList⌝⦄ setPeer pid p
    ⦃⇓? _ w => ⌜P (routingView w)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hi hr
  cases x
  cases hd : w.dev with
  | none => simp [hd] at hi
  | some d =>
    obtain ⟨old, hold, hl⟩ := Option.map_eq_some_iff.mp (by simpa [hd] using hi.2)
    have he := routingState_insert_same d pid old p hold hl.symm
    cases hr
    simpa [routingView, setPeer, modifyDev, hd, he] using hi.1

/-- Any actual state carrier may project to native WG state. The original
seven store observations suffice; product callbacks remain in scope. -/
theorem routing_kernel {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} (a : StateT S m α)
    (ha : SameView (fun s => wgStoreView (project s)) a) :
    SameView (fun s => routingView (project s)) a :=
  ha.of_factor (fun s : WGStoreView => s.dev.map routingState)
    (fun s => routingView (project s)) (fun _ => rfl)

theorem dstCacheReset_routing (pid : PeerId) : SameView routingView (dstCacheReset pid) := by
  intro initial
  have ambient {α : Type} (a : AmbientM α) :
      Preserves (fun w => routingView w = initial) (monadLift a : WG.M α) :=
    hoare_liftAmbient a _
  have readBind {α : Type} (pid : PeerId) (f : Peer → WG.M α)
      (hf : ∀ p, initial.bind (fun view => view.lists pid) = some p.allowedipsList →
        Preserves (fun w => routingView w = initial) (f p)) :
      Preserves (fun w => routingView w = initial) (getPeer pid >>= f) := by
    apply hoare_bind _ _ (routing_getPeer (fun view => view = initial) pid)
    intro p
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a x v b h hr
    have saved : (routingView w).bind (fun view => view.lists pid) = some p.allowedipsList := by
      simpa only [routingView, routingState, Option.bind_map, Function.comp_def] using h.2
    rw [h.1] at saved
    exact (hoare_iff_run_ambient _ _ _).mp (hf p saved) w a x v b h.1 hr
  have knownSet (pid : PeerId) (p : Peer)
      (hp : initial.bind (fun view => view.lists pid) = some p.allowedipsList) :
      Preserves (fun w => routingView w = initial) (setPeer pid p) := by
    apply hoare_consequence (routing_setPeer (fun view => view = initial) pid p)
    · intro w h
      refine ⟨h, ?_⟩
      have current : (routingView w).bind (fun view => view.lists pid) = some p.allowedipsList := by
        rw [h]; exact hp
      simpa only [routingView, routingState, Option.bind_map, Function.comp_def] using current
    · exact fun _ _ h => h
  have read : Preserves (fun w => routingView w = initial) (get : WG.M WGWorld) :=
    hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2)
  unfold dstCacheReset getAmbient
  apply preserves_bind (ambient (get : AmbientM Ambient))
  intro a
  apply preserves_bind read
  intro g
  split
  · exact preserves_pure ()
  · apply preserves_bind (ambient (AmbientM.hiddenJiffies .dstCacheResetTs))
    intro ts
    apply readBind
    intro p hp
    exact knownSet pid {p with dstCache := {p.dstCache with resetTs := ts}} hp

theorem resetLastSentHandshake_routing (pid : PeerId) : SameView routingView (resetLastSentHandshake pid) := by
  intro initial
  have ambient {α : Type} (a : AmbientM α) :
      Preserves (fun w => routingView w = initial) (monadLift a : WG.M α) :=
    hoare_liftAmbient a _
  have readBind {α : Type} (pid : PeerId) (f : Peer → WG.M α)
      (hf : ∀ p, initial.bind (fun view => view.lists pid) = some p.allowedipsList →
        Preserves (fun w => routingView w = initial) (f p)) :
      Preserves (fun w => routingView w = initial) (getPeer pid >>= f) := by
    apply hoare_bind _ _ (routing_getPeer (fun view => view = initial) pid)
    intro p
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a x v b h hr
    have saved : (routingView w).bind (fun view => view.lists pid) = some p.allowedipsList := by
      simpa only [routingView, routingState, Option.bind_map, Function.comp_def] using h.2
    rw [h.1] at saved
    exact (hoare_iff_run_ambient _ _ _).mp (hf p saved) w a x v b h.1 hr
  have knownSet (pid : PeerId) (p : Peer)
      (hp : initial.bind (fun view => view.lists pid) = some p.allowedipsList) :
      Preserves (fun w => routingView w = initial) (setPeer pid p) := by
    apply hoare_consequence (routing_setPeer (fun view => view = initial) pid p)
    · intro w h
      refine ⟨h, ?_⟩
      have current : (routingView w).bind (fun view => view.lists pid) = some p.allowedipsList := by
        rw [h]; exact hp
      simpa only [routingView, routingState, Option.bind_map, Function.comp_def] using current
    · exact fun _ _ h => h
  unfold resetLastSentHandshake
  apply preserves_bind (ambient (AmbientM.hiddenClock64 .resetLastSent))
  intro now
  apply readBind
  intro p hp
  exact knownSet pid {p with lastSentHandshake :=
    now - (REKEY_TIMEOUT + 1 : Nat).toInt64 * NSEC_PER_SEC64} hp

theorem precomputeStaticStatic_routing (pid : PeerId) : SameView routingView (precomputeStaticStatic pid) := by
  intro initial
  have ambient {α : Type} (a : AmbientM α) :
      Preserves (fun w => routingView w = initial) (monadLift a : WG.M α) :=
    hoare_liftAmbient a _
  have readBind {α : Type} (pid : PeerId) (f : Peer → WG.M α)
      (hf : ∀ p, initial.bind (fun view => view.lists pid) = some p.allowedipsList →
        Preserves (fun w => routingView w = initial) (f p)) :
      Preserves (fun w => routingView w = initial) (getPeer pid >>= f) := by
    apply hoare_bind _ _ (routing_getPeer (fun view => view = initial) pid)
    intro p
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a x v b h hr
    have saved : (routingView w).bind (fun view => view.lists pid) = some p.allowedipsList := by
      simpa only [routingView, routingState, Option.bind_map, Function.comp_def] using h.2
    rw [h.1] at saved
    exact (hoare_iff_run_ambient _ _ _).mp (hf p saved) w a x v b h.1 hr
  have knownSet (pid : PeerId) (p : Peer)
      (hp : initial.bind (fun view => view.lists pid) = some p.allowedipsList) :
      Preserves (fun w => routingView w = initial) (setPeer pid p) := by
    apply hoare_consequence (routing_setPeer (fun view => view = initial) pid p)
    · intro w h
      refine ⟨h, ?_⟩
      have current : (routingView w).bind (fun view => view.lists pid) = some p.allowedipsList := by
        rw [h]; exact hp
      simpa only [routingView, routingState, Option.bind_map, Function.comp_def] using current
    · exact fun _ _ h => h
  have device : Preserves (fun w => routingView w = initial) getDev := by
    unfold getDev
    apply preserves_bind (hoare_consequence (hoare_get (fun w => routingView w = initial))
      (fun _ h => h) (fun _ _ h => h.2))
    intro w
    cases w.dev
    · exact ambient (AmbientM.invariant _)
    · exact preserves_pure _
  unfold precomputeStaticStatic
  simp only [requireNotPending, pure_bind]
  apply preserves_bind device
  intro d
  apply readBind
  intro p hp
  apply preserves_bind (ambient (AmbientM.branch .precomputeNoIdentity !d.staticIdentity.hasIdentity))
  intro noIdentity
  cases noIdentity <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · apply preserves_bind (knownSet pid {p with precomputedStaticStatic :=
      (curve25519 d.staticIdentity.staticPrivate p.remoteStatic).1} hp)
    intro _
    apply preserves_bind (ambient (AmbientM.branch .precomputeNullPoint
      !(curve25519 d.staticIdentity.staticPrivate p.remoteStatic).2))
    intro zero
    cases zero <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact preserves_pure ()
    · apply readBind
      intro q hq
      exact knownSet pid {q with precomputedStaticStatic := List.replicate 32 0} hq
  · apply readBind
    intro q hq
    exact knownSet pid {q with precomputedStaticStatic := List.replicate 32 0} hq

theorem handshakeInit_routing (pid : PeerId) (psk : Option Key) : SameView routingView (handshakeInit pid psk) := by
  intro initial
  have ambient {α : Type} (a : AmbientM α) :
      Preserves (fun w => routingView w = initial) (monadLift a : WG.M α) :=
    hoare_liftAmbient a _
  have readBind {α : Type} (pid : PeerId) (f : Peer → WG.M α)
      (hf : ∀ p, initial.bind (fun view => view.lists pid) = some p.allowedipsList →
        Preserves (fun w => routingView w = initial) (f p)) :
      Preserves (fun w => routingView w = initial) (getPeer pid >>= f) := by
    apply hoare_bind _ _ (routing_getPeer (fun view => view = initial) pid)
    intro p
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a x v b h hr
    have saved : (routingView w).bind (fun view => view.lists pid) = some p.allowedipsList := by
      simpa only [routingView, routingState, Option.bind_map, Function.comp_def] using h.2
    rw [h.1] at saved
    exact (hoare_iff_run_ambient _ _ _).mp (hf p saved) w a x v b h.1 hr
  have knownSet (pid : PeerId) (p : Peer)
      (hp : initial.bind (fun view => view.lists pid) = some p.allowedipsList) :
      Preserves (fun w => routingView w = initial) (setPeer pid p) := by
    apply hoare_consequence (routing_setPeer (fun view => view = initial) pid p)
    · intro w h
      refine ⟨h, ?_⟩
      have current : (routingView w).bind (fun view => view.lists pid) = some p.allowedipsList := by
        rw [h]; exact hp
      simpa only [routingView, routingState, Option.bind_map, Function.comp_def] using current
    · exact fun _ _ h => h
  unfold handshakeInit IndexOwner.setPeerWord
  apply preserves_bind
  · apply readBind
    intro p hp
    exact knownSet pid {p with handshakeEntryPeer := some pid} hp
  · intro _
    apply preserves_bind (ambient (AmbientM.branch .handshakeInitHasPsk psk.isSome))
    intro hasPsk
    cases hasPsk
    · exact (precomputeStaticStatic_routing pid).wp (fun view => view = initial)
    · apply readBind
      intro p hp
      apply preserves_bind (knownSet pid {p with presharedKey := psk.getD p.presharedKey} hp)
      intro _
      exact (precomputeStaticStatic_routing pid).wp (fun view => view = initial)

end Leanux.Proofs.WG.AllowedIps
