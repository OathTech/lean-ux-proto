import Leanux.Proofs.WG.Lifetimes.MaintenanceTimers

/-! Reads from a saved peer-map snapshot. Capturing a map is not a resolved
peer read; each demanded predicate emits the saved entry's identity. Safety
requires its stamp to remain current.
No extra getter is inserted into the observed source execution. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

abbrev SavedPeers (xs : List (PeerId × Peer)) (s : IdentityView) : Prop :=
  ∀ id p, (id, p) ∈ xs → s.1.slots id = some p.internalId

def savedPeerRead (id : PeerId) (p : Peer) : MixedM Unit :=
  emitStatePrefix (.peer (.read id p.internalId))

theorem savedPeerRead_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (id : PeerId) (p : Peer) :
    AmbientSpec I (fun s => P s ∧ s.1.slots id = some p.internalId)
      (savedPeerRead id p) (fun _ s => P s ∧ s.1.slots id = some p.internalId) := by
  intro w ambient h hi
  have live := hi.2.2
  change (Peers.snapshot w).slots id = some p.internalId at live
  cases hd : w.dev with
  | none => simp [Peers.snapshot, hd] at live
  | some d =>
    cases hp : d.peers[id]? with
    | none => simp [Peers.snapshot, hd, hp] at live
    | some q =>
      have stamp : q.internalId = p.internalId := by simpa [Peers.snapshot, hd, hp] using live
      have hr : ((getPeer id).run w).run ambient = .ok ((q, w), ambient) := by
        simp [getPeer, getDev, hd, hp]
      have obs := c.getPeer (fun s => P s ∧ s.1.slots id = some p.internalId) id w ambient h hi
      rw [show runPrefix ((getPeerMixed id).run w) ambient h =
          runStatePrefix (getPeerMixed id) w ambient h from rfl, getPeerMixed_run, hr] at obs
      obtain ⟨suffix, he, hs, hout⟩ := obs
      simp only [stamp] at hs hout
      exact ⟨[.peer (.read id p.internalId)], rfl, hs, hout.1, hi.2⟩

theorem getDev_saved_spec (c : AmbientContracts I) (P : IdentityView → Prop) :
    AmbientSpec I P (liftWGPrefix getDev) (fun d s => P s ∧ SavedPeers d.peers.toList s) := by
  apply StatePrefixEnsures.lift _ (fun h w _ hi => c.safe h w hi.1)
  intro h w ambient d v ambient' hi hr
  cases hd : w.dev with
  | none =>
    simp [getDev, hd, invariant, AmbientM.invariant] at hr
    cases hr
  | some actual =>
    have he : (getDev.run w).run ambient = .ok ((actual, w), ambient) := by simp [getDev, hd]
    rw [he] at hr
    cases hr
    refine ⟨hi.1, hi.2, ?_⟩
    intro id p hp
    have entry := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hp
    simp [identityView, Peers.snapshot, hd, entry]

def savedPeerAny (test : Peer → Bool) : List (PeerId × Peer) → MixedM Bool
  | [] => pure false
  | (id, p) :: rest => do
    savedPeerRead id p
    if test p then pure true else savedPeerAny test rest

def savedPeerAnyEvents (test : Peer → Bool) : List (PeerId × Peer) → List LifetimeEvent
  | [] => []
  | (id, p) :: rest => .peer (.read id p.internalId) ::
      (if test p then [] else savedPeerAnyEvents test rest)

theorem savedPeerAny_run (test : Peer → Bool) (xs : List (PeerId × Peer)) (w : WGWorld) (ambient : Ambient) (h : List LifetimeEvent) :
    runStatePrefix (savedPeerAny test xs) w ambient h =
      (.ok ((xs.any (fun x => test x.2), w), ambient), h ++ savedPeerAnyEvents test xs) := by
  induction xs generalizing h with
  | nil => simp [savedPeerAny, savedPeerAnyEvents]
  | cons x xs ih =>
    rcases x with ⟨id,p⟩
    simp only [savedPeerAny, savedPeerRead, runStatePrefix_bind, runStatePrefix_emit]
    cases ht : test p <;> simp [ht, ih, savedPeerAnyEvents, List.any_cons, List.append_assoc]

theorem savedPeerAny_erases (test : Peer → Bool) (xs : List (PeerId × Peer)) :
    ErasesStatePrefix (savedPeerAny test xs) (pure (xs.any (fun x => test x.2))) := by
  intro w ambient h
  change (runStatePrefix _ w ambient h).1 = _
  rw [savedPeerAny_run]
  rfl

theorem savedPeerAny_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (test : Peer → Bool) (xs : List (PeerId × Peer)) :
    AmbientSpec I (fun s => P s ∧ SavedPeers xs s) (savedPeerAny test xs) (fun _ => P) := by
  induction xs with
  | nil =>
    exact (c.pure (fun s => P s ∧ SavedPeers [] s) false).consequence
      (fun _ _ _ hi => hi) (fun _ _ _ _ hi => ⟨hi.1, hi.2.1⟩)
  | cons x xs ih =>
    rcases x with ⟨id,p⟩
    unfold savedPeerAny
    have hread : AmbientSpec I (fun s => P s ∧ SavedPeers ((id,p)::xs) s)
        (savedPeerRead id p) (fun _ s => P s ∧ SavedPeers xs s) :=
      (savedPeerRead_spec c (fun s => P s ∧ SavedPeers xs s) id p).consequence
      (fun _ _ _ hi => ⟨hi.1, ⟨hi.2.1, fun i q hq => hi.2.2 i q (by simp [hq])⟩,
        hi.2.2 id p (by simp)⟩) (fun _ _ _ _ hi => ⟨hi.1, hi.2.1⟩)
    apply StatePrefixEnsures.bind hread
    intro _
    split
    · exact (c.pure (fun s => P s ∧ SavedPeers xs s) true).consequence
        (fun _ _ _ hi => hi) (fun _ _ _ _ hi => ⟨hi.1, hi.2.1⟩)
    · exact ih

/-- An eager map over a captured peer store. Every tested entry, including
misses, emits its saved identity before the pure predicate is evaluated. -/
def savedPeerFilterMap (f : PeerId → Peer → Option α) : List (PeerId × Peer) → MixedM (List α)
  | [] => pure []
  | (id, p) :: rest => do
    savedPeerRead id p
    let tail ← savedPeerFilterMap f rest
    return match f id p with | none => tail | some x => x :: tail

theorem savedPeerFilterMap_run (f : PeerId → Peer → Option α)
    (xs : List (PeerId × Peer)) (w : WGWorld) (ambient : Ambient) (h : List LifetimeEvent) :
    runStatePrefix (savedPeerFilterMap f xs) w ambient h =
      (.ok ((xs.filterMap (fun x => f x.1 x.2), w), ambient),
        h ++ xs.map (fun x => LifetimeEvent.peer (.read x.1 x.2.internalId))) := by
  induction xs generalizing h with
  | nil => simp [savedPeerFilterMap]
  | cons x xs ih =>
    rcases x with ⟨id,p⟩
    simp only [savedPeerFilterMap, savedPeerRead, runStatePrefix_bind, runStatePrefix_emit, ih]
    cases hf : f id p <;> simp [hf, List.append_assoc]

theorem savedPeerFilterMap_erases (f : PeerId → Peer → Option α) (xs : List (PeerId × Peer)) :
    ErasesStatePrefix (savedPeerFilterMap f xs) (pure (xs.filterMap (fun x => f x.1 x.2))) := by
  intro w ambient h
  change (runStatePrefix _ w ambient h).1 = _
  rw [savedPeerFilterMap_run]
  rfl

theorem savedPeerFilterMap_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (f : PeerId → Peer → Option α) (xs : List (PeerId × Peer)) :
    AmbientSpec I (fun s => P s ∧ SavedPeers xs s) (savedPeerFilterMap f xs) (fun _ => P) := by
  induction xs with
  | nil =>
    exact (c.pure (fun s => P s ∧ SavedPeers [] s) []).consequence
      (fun _ _ _ hi => hi) (fun _ _ _ _ hi => ⟨hi.1, hi.2.1⟩)
  | cons x xs ih =>
    rcases x with ⟨id,p⟩
    unfold savedPeerFilterMap
    have hread : AmbientSpec I (fun s => P s ∧ SavedPeers ((id,p)::xs) s)
        (savedPeerRead id p) (fun _ s => P s ∧ SavedPeers xs s) :=
      (savedPeerRead_spec c (fun s => P s ∧ SavedPeers xs s) id p).consequence
      (fun _ _ _ hi => ⟨hi.1, ⟨hi.2.1, fun i q hq => hi.2.2 i q (by simp [hq])⟩,
        hi.2.2 id p (by simp)⟩) (fun _ _ _ _ hi => ⟨hi.1, hi.2.1⟩)
    exact StatePrefixEnsures.bind hread (fun _ => StatePrefixEnsures.bind ih (fun _ => c.pure P _))

/-- The saved-read contract also retains arbitrary invariants over the actual product. -/
theorem savedPeerRead_spec_product (c : ProductAmbientContracts I) (P : IdentityView → Prop)
    (id : PeerId) (p : Peer) :
    ProductAmbientSpec I (fun s => P s ∧ s.1.slots id = some p.internalId)
      (liftWGObserver (savedPeerRead id p))
      (fun _ s => P s ∧ s.1.slots id = some p.internalId) := by
  intro w h hi
  have live := hi.2.2
  change (Peers.snapshot w.wg).slots id = some p.internalId at live
  cases hd : w.wg.dev with
  | none => simp [Peers.snapshot, hd] at live
  | some d =>
    cases hp : d.peers[id]? with
    | none => simp [Peers.snapshot, hd, hp] at live
    | some q =>
      have stamp : q.internalId = p.internalId := by simpa [Peers.snapshot, hd, hp] using live
      have hr : ((getPeer id).run w.wg).run w.ambient = .ok ((q, w.wg), w.ambient) := by
        simp [getPeer, getDev, hd, hp]
      have obs := c.getPeer (fun s => P s ∧ s.1.slots id = some p.internalId) id w h hi
      rw [liftWGObserver_run, runWGPrefix, getPeerMixed_run, hr] at obs
      obtain ⟨suffix, he, hs, hout⟩ := obs
      simp only [stamp, Except.map] at hs hout
      exact ⟨[.peer (.read id p.internalId)], rfl, hs, hout.1, hi.2⟩

theorem getDev_saved_spec_product (c : ProductAmbientContracts I) (P : IdentityView → Prop) :
    ProductAmbientSpec I P (liftWGObserver (liftWGPrefix getDev))
      (fun d s => P s ∧ SavedPeers d.peers.toList s) := by
  rw [liftWGObserver_lift]
  apply PrefixEnsures.lift _ (fun h w hi => c.safe h w hi.1)
  intro h w d v hi hr
  rw [liftWG_run] at hr
  cases hd : w.wg.dev with
  | none =>
    simp [getDev, hd, invariant, AmbientM.invariant] at hr
    cases hr
  | some actual =>
    have he : (getDev.run w.wg).run w.ambient = .ok ((actual, w.wg), w.ambient) := by
      simp [getDev, hd]
    rw [he] at hr
    cases hr
    refine ⟨hi.1, hi.2, ?_⟩
    intro id p hp
    have entry := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hp
    simp [identityView, Peers.snapshot, hd, entry]

theorem savedPeerAny_spec_product (c : ProductAmbientContracts I) (P : IdentityView → Prop)
    (test : Peer → Bool) (xs : List (PeerId × Peer)) :
    ProductAmbientSpec I (fun s => P s ∧ SavedPeers xs s)
      (liftWGObserver (savedPeerAny test xs)) (fun _ => P) := by
  induction xs with
  | nil =>
    simpa only [savedPeerAny, liftWGObserver_pure] using
      (c.pure (fun s => P s ∧ SavedPeers [] s) false).consequence
        (fun _ _ hi => hi) (fun _ _ _ hi => ⟨hi.1, hi.2.1⟩)
  | cons x xs ih =>
    rcases x with ⟨id,p⟩
    rw [savedPeerAny, liftWGObserver_bind]
    have hread : ProductAmbientSpec I (fun s => P s ∧ SavedPeers ((id,p)::xs) s)
        (liftWGObserver (savedPeerRead id p)) (fun _ s => P s ∧ SavedPeers xs s) :=
      (savedPeerRead_spec_product c (fun s => P s ∧ SavedPeers xs s) id p).consequence
        (fun _ _ hi => ⟨hi.1, ⟨hi.2.1, fun i q hq => hi.2.2 i q (by simp [hq])⟩,
          hi.2.2 id p (by simp)⟩) (fun _ _ _ hi => ⟨hi.1, hi.2.1⟩)
    apply PrefixEnsures.bind hread
    intro _
    split
    · simpa only [liftWGObserver_pure] using
        (c.pure (fun s => P s ∧ SavedPeers xs s) true).consequence
          (fun _ _ hi => hi) (fun _ _ _ hi => ⟨hi.1, hi.2.1⟩)
    · exact ih

theorem savedPeerFilterMap_spec_product (c : ProductAmbientContracts I) (P : IdentityView → Prop)
    (f : PeerId → Peer → Option α) (xs : List (PeerId × Peer)) :
    ProductAmbientSpec I (fun s => P s ∧ SavedPeers xs s)
      (liftWGObserver (savedPeerFilterMap f xs)) (fun _ => P) := by
  induction xs with
  | nil =>
    simpa only [savedPeerFilterMap, liftWGObserver_pure] using
      (c.pure (fun s => P s ∧ SavedPeers [] s) []).consequence
        (fun _ _ hi => hi) (fun _ _ _ hi => ⟨hi.1, hi.2.1⟩)
  | cons x xs ih =>
    rcases x with ⟨id,p⟩
    rw [savedPeerFilterMap, liftWGObserver_bind]
    have hread : ProductAmbientSpec I (fun s => P s ∧ SavedPeers ((id,p)::xs) s)
        (liftWGObserver (savedPeerRead id p)) (fun _ s => P s ∧ SavedPeers xs s) :=
      (savedPeerRead_spec_product c (fun s => P s ∧ SavedPeers xs s) id p).consequence
        (fun _ _ hi => ⟨hi.1, ⟨hi.2.1, fun i q hq => hi.2.2 i q (by simp [hq])⟩,
          hi.2.2 id p (by simp)⟩) (fun _ _ _ hi => ⟨hi.1, hi.2.1⟩)
    apply PrefixEnsures.bind hread
    intro _
    rw [liftWGObserver_bind]
    apply PrefixEnsures.bind ih
    intro tail
    simpa only [liftWGObserver_pure] using c.pure P (match f id p with | none => tail | some x => x :: tail)

end Leanux.Proofs.WG.Lifetimes
