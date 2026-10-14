import Leanux.Proofs.WG.AllowedIps.RoutingHistory

/-! Routing transport which permits resident-peer deletion. Surviving lists
come from the same input slot; raw trie owners need not remain resident. This
relation preserves device presence and is not a creation/destruction contract. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG

structure RoutingState.Retains (before after : RoutingState) : Prop where
  nodes : after.nodes = before.nodes
  table : after.table = before.table
  nodeFrontier : after.nodeFrontier = before.nodeFrontier
  peerFrontier : after.peerFrontier = before.peerFrontier
  lists : ∀ pid ids, after.lists pid = some ids → before.lists pid = some ids

def RetainsRouting : Option RoutingState → Option RoutingState → Prop
  | none, none => True
  | some before, some after => before.Retains after
  | _, _ => False

theorem RetainsRouting.refl (s : Option RoutingState) : RetainsRouting s s := by
  cases s with
  | none => trivial
  | some s => exact ⟨rfl, rfl, rfl, rfl, fun _ _ h => h⟩

theorem RetainsRouting.trans (h : RetainsRouting a b) (g : RetainsRouting b c) :
    RetainsRouting a c := by
  cases a <;> cases b <;> cases c <;> try contradiction
  · trivial
  · exact ⟨g.nodes.trans h.nodes, g.table.trans h.table,
      g.nodeFrontier.trans h.nodeFrontier, g.peerFrontier.trans h.peerFrontier,
      fun pid ids hi => h.lists pid ids (g.lists pid ids hi)⟩

theorem RoutingInvariant.of_retains (hi : RoutingInvariant d t4 t6)
    (h : (routingState d).Retains (routingState out)) : RoutingInvariant out t4 t6 := by
  have hn : out.nodes = d.nodes := h.nodes
  have ht : out.peerAllowedips = d.peerAllowedips := h.table
  have hnf : out.nextNode = d.nextNode := h.nodeFrontier
  have hpf : out.nextPeer = d.nextPeer := h.peerFrontier
  have origin (pid : PeerId) (p : Peer) (hp : out.peers[pid]? = some p) :
      ∃ old, d.peers[pid]? = some old ∧ old.allowedipsList = p.allowedipsList := by
    apply Option.map_eq_some_iff.mp
    exact h.lists pid p.allowedipsList (by simp [routingState, hp])
  refine ⟨?_, hi.valid4, hi.valid6, hi.compressed4, hi.compressed6,
    hi.nodup4, hi.nodup6, ?_, ?_, ?_, ?_⟩
  · simpa only [ForestRep, hn, ht] using hi.forest
  · simpa only [NodesBelow, hn, hnf] using hi.below
  · intro pid p hp
    obtain ⟨old, hold, hl⟩ := origin pid p hp
    simpa only [hl] using hi.lists pid old hold
  · simpa only [OwnersBelow, hpf] using hi.owners
  · intro pid p hp
    obtain ⟨old, hold, _⟩ := origin pid p hp
    rw [hpf]
    exact hi.peerSlots pid old hold

def RoutedView (view : Option RoutingState) (xs : FlatTable × FlatTable) : Prop :=
  ∃ d t4 t6, view = some (routingState d) ∧ RoutingInvariant d t4 t6 ∧
    FlatAgree 32 t4 xs.1 ∧ FlatAgree 128 t6 xs.2

theorem RoutedView.realize (h : RoutedView (routingView w) xs) :
    ∃ d t4 t6, w.k.wg = some d ∧ RoutingInvariant d t4 t6 ∧
      FlatAgree 32 t4 xs.1 ∧ FlatAgree 128 t6 xs.2 := by
  obtain ⟨old, t4, t6, hv, hi, h4, h6⟩ := h
  obtain ⟨d, hd, he⟩ := Option.map_eq_some_iff.mp hv
  exact ⟨d, t4, t6, hd, hi.of_routingState he, h4, h6⟩

theorem RoutedView.retains (hi : RoutedView a xs) (h : RetainsRouting a (routingView w)) :
    RoutedView (routingView w) xs := by
  obtain ⟨d, t4, t6, rfl, hd, h4, h6⟩ := hi
  cases hw : w.k.wg with
  | none => simp [routingView, hw, RetainsRouting] at h
  | some out =>
    have hr : (routingState d).Retains (routingState out) := by
      simpa [routingView, hw, RetainsRouting] using h
    exact ⟨out, t4, t6, by simp [routingView, hw], hd.of_retains hr, h4, h6⟩

def RoutingResident (pid : PeerId) (view : Option RoutingState) : Prop :=
  ∃ s ids, view = some s ∧ s.lists pid = some ids

theorem RoutingResident.realize (h : RoutingResident pid (routingView w))
    (hd : w.k.wg = some d) : ∃ p, d.peers[pid]? = some p := by
  obtain ⟨s, ids, hs, hl⟩ := h
  simp only [routingView, hd, Option.map_some, Option.some.injEq] at hs
  subst s
  obtain ⟨p, hp, _⟩ := Option.map_eq_some_iff.mp hl
  exact ⟨p, hp⟩

theorem routingResident_of_peer (hd : w.k.wg = some d) (hp : d.peers[pid]? = some p) :
    RoutingResident pid (routingView w) := by
  exact ⟨routingState d, p.allowedipsList, by simp [routingView, hd], by simp [routingState, hp]⟩

def RetainsRoutingCall (a : M α) : Prop :=
  ∀ w x v, a.run w = .ok (x, v) → RetainsRouting (routingView w) (routingView v)

theorem RetainsRoutingCall.of_same (h : Leanux.Proofs.Framing.SameView routingView a) :
    RetainsRoutingCall a := by
  intro w x v hr
  rw [h w x v hr]
  exact RetainsRouting.refl _

theorem peerPut_retainsRouting (peer : Option PeerId) : RetainsRoutingCall (peerPut peer) := by
  intro w x v hr
  cases x
  have hs := (Leanux.Proofs.Framing.hoare_iff_triple _ _ _).mpr (peerPut_routing_spec w peer) w () v rfl hr
  rcases hs with he | ⟨pid, he⟩
  · rw [he]; exact RetainsRouting.refl _
  · rw [he]
    cases hv : routingView w with
    | none => trivial
    | some s =>
      refine ⟨rfl, rfl, rfl, rfl, ?_⟩
      intro q ids hq
      change (if q = pid then none else s.lists q) = some ids at hq
      split at hq <;> simp_all

end Leanux.Proofs.WG.AllowedIps
