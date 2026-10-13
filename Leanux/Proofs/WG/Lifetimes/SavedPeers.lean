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
  emitPrefix (.peer (.read id p.internalId))

theorem savedPeerRead_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (id : PeerId) (p : Peer) :
    AmbientSpec I (fun s => P s ∧ s.1.slots id = some p.internalId)
      (savedPeerRead id p) (fun _ s => P s ∧ s.1.slots id = some p.internalId) := by
  intro w h hi
  have live := hi.2.2
  change (Peers.snapshot w).slots id = some p.internalId at live
  cases hd : w.k.wg with
  | none => simp [Peers.snapshot, hd] at live
  | some d =>
    cases hp : d.peers[id]? with
    | none => simp [Peers.snapshot, hd, hp] at live
    | some q =>
      have stamp : q.internalId = p.internalId := by simpa [Peers.snapshot, hd, hp] using live
      have hr : (getPeer id).run w = .ok (q, w) := by simp [getPeer, getDev, getK, hd, hp]
      have obs := c.getPeer (fun s => P s ∧ s.1.slots id = some p.internalId) id w h hi
      rw [getPeerMixed_run, hr] at obs
      obtain ⟨suffix, he, hs, hout⟩ := obs
      simp only [stamp] at hs hout
      exact ⟨[.peer (.read id p.internalId)], rfl, hs, hout.1, hi.2⟩

theorem getDev_saved_spec (c : AmbientContracts I) (P : IdentityView → Prop) :
    AmbientSpec I P (liftPrefix getDev) (fun d s => P s ∧ SavedPeers d.peers.toList s) := by
  apply PrefixEnsures.lift _ (fun h w hi => c.safe h w hi.1)
  intro h w d v hi hr
  cases hd : w.k.wg with
  | none => simp [getDev, getK, hd, invariant] at hr
  | some actual =>
    have he : getDev.run w = .ok (actual, w) := by simp [getDev, getK, hd]
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

theorem savedPeerAny_run (test : Peer → Bool) (xs : List (PeerId × Peer)) (w : World) (h : List LifetimeEvent) :
    runPrefix (savedPeerAny test xs) w h =
      (.ok (xs.any (fun x => test x.2), w), h ++ savedPeerAnyEvents test xs) := by
  induction xs generalizing h with
  | nil => simp [savedPeerAny, savedPeerAnyEvents]
  | cons x xs ih =>
    rcases x with ⟨id,p⟩
    simp only [savedPeerAny, savedPeerRead, runPrefix_bind, runPrefix_emit]
    cases ht : test p <;> simp [ht, ih, savedPeerAnyEvents, List.any_cons, List.append_assoc]

theorem savedPeerAny_erases (test : Peer → Bool) (xs : List (PeerId × Peer)) :
    ErasesPrefix (savedPeerAny test xs) (pure (xs.any (fun x => test x.2))) := by
  intro w h
  rw [savedPeerAny_run]
  rfl

theorem savedPeerAny_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (test : Peer → Bool) (xs : List (PeerId × Peer)) :
    AmbientSpec I (fun s => P s ∧ SavedPeers xs s) (savedPeerAny test xs) (fun _ => P) := by
  induction xs with
  | nil =>
    exact (c.pure (fun s => P s ∧ SavedPeers [] s) false).consequence
      (fun _ _ hi => hi) (fun _ _ _ hi => ⟨hi.1, hi.2.1⟩)
  | cons x xs ih =>
    rcases x with ⟨id,p⟩
    unfold savedPeerAny
    have hread : AmbientSpec I (fun s => P s ∧ SavedPeers ((id,p)::xs) s)
        (savedPeerRead id p) (fun _ s => P s ∧ SavedPeers xs s) :=
      (savedPeerRead_spec c (fun s => P s ∧ SavedPeers xs s) id p).consequence
      (fun _ _ hi => ⟨hi.1, ⟨hi.2.1, fun i q hq => hi.2.2 i q (by simp [hq])⟩,
        hi.2.2 id p (by simp)⟩) (fun _ _ _ hi => ⟨hi.1, hi.2.1⟩)
    apply PrefixEnsures.bind hread
    intro _
    split
    · exact (c.pure (fun s => P s ∧ SavedPeers xs s) true).consequence
        (fun _ _ hi => hi) (fun _ _ _ hi => ⟨hi.1, hi.2.1⟩)
    · exact ih

end Leanux.Proofs.WG.Lifetimes
