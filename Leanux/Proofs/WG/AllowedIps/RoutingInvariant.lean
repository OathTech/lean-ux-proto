import Leanux.Proofs.WG.AllowedIps.InsertionCoherence
import Leanux.Proofs.WG.AllowedIps.RemovalPeer

/-! A conditional routing invariant for the two represented families. Owner
labels are bounded by the allocator frontier, not required to be resident. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux
set_option pp.structureInstances false

def OwnersBelow (d : WG.Device) (t4 t6 : Tree) : Prop :=
  ∀ e ∈ t4.entries ++ t6.entries, e.peer < d.nextPeer

def PeerSlotsBelow (d : WG.Device) : Prop :=
  ∀ pid p, d.peers[pid]? = some p → pid < d.nextPeer

structure RoutingInvariant (d : WG.Device) (t4 t6 : Tree) : Prop where
  forest : ForestRep d t4 t6
  valid4 : t4.Valid 32
  valid6 : t6.Valid 128
  compressed4 : t4.Compressed
  compressed6 : t6.Compressed
  nodup4 : t4.nodeIds.Nodup
  nodup6 : t6.nodeIds.Nodup
  below : NodesBelow d
  lists : ResidentLists d t4 t6
  owners : OwnersBelow d t4 t6
  peerSlots : PeerSlotsBelow d

theorem OwnersBelow.swap (h : OwnersBelow d a b) : OwnersBelow d b a := by
  intro e he
  apply h e
  simpa only [List.mem_append, or_comm] using he

theorem Inserted.nextPeer (h : Inserted d out v4 t other addr cidr pid) :
    out.nextPeer = d.nextPeer := by
  have he := congrArg WG.Device.nextPeer h.frame
  exact he

theorem Inserted.peerSlots (h : Inserted d out v4 t other addr cidr pid)
    (hb : PeerSlotsBelow d) : PeerSlotsBelow out := by
  intro q p hp
  rw [h.peers] at hp
  obtain ⟨old, hold, _⟩ := Option.map_eq_some_iff.mp hp
  rw [h.nextPeer]
  exact hb q old hold

theorem Inserted.owners (h : Inserted d out v4 t other addr cidr pid)
    (hv : t.Valid (rootWidth v4)) (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
    (ho : OwnersBelow d t other) (hp : pid < d.nextPeer) :
    OwnersBelow out (t.insertFresh (rootWidth v4) d.nextNode addr cidr pid).tree other := by
  intro e he
  rw [h.nextPeer]
  rcases List.mem_append.mp he with he | he
  · rcases (Tree.insertFresh_entries hv ha hc d.nextNode pid e).mp he with rfl | ⟨he, _⟩
    · simpa only [Tree.insertFresh_peer] using hp
    · exact ho e (List.mem_append_left _ he)
  · exact ho e (List.mem_append_right _ he)

def selectedTree (v4 : Bool) (t4 t6 : Tree) : Tree := if v4 then t4 else t6

def insertedTree4 (d : WG.Device) (v4 : Bool) (t4 : Tree) (addr cidr pid : Nat) : Tree :=
  if v4 then (t4.insertFresh 32 d.nextNode addr cidr pid).tree else t4

def insertedTree6 (d : WG.Device) (v4 : Bool) (t6 : Tree) (addr cidr pid : Nat) : Tree :=
  if v4 then t6 else (t6.insertFresh 128 d.nextNode addr cidr pid).tree

theorem RoutingInvariant.inserted (hi : RoutingInvariant d t4 t6)
    (v4 : Bool) (addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
    (h : Inserted d out v4 (selectedTree v4 t4 t6) (selectedTree (!v4) t4 t6) addr cidr pid) :
    RoutingInvariant out (insertedTree4 d v4 t4 addr cidr pid) (insertedTree6 d v4 t6 addr cidr pid) := by
  have hpid := hi.peerSlots pid p hp
  cases v4
  · have ht : Inserted d out false t6 t4 addr cidr pid := h
    refine ⟨⟨?_, ?_, ht.otherRep, ht.rep⟩, hi.valid4,
      Tree.insertFresh_valid hi.valid6 ha hc d.nextNode pid,
      hi.compressed4, Tree.insertFresh_compressed hi.compressed6 128 d.nextNode addr cidr pid,
      hi.nodup4, Tree.insertFresh_nodeIds_nodup hi.nodup6 (hi.forest.2.2.2.ids_below hi.below) 128 addr cidr pid,
      ht.below, ?_, ?_, ht.peerSlots hi.peerSlots⟩
    · exact ht.otherRoot.trans hi.forest.1
    · exact ht.root
    · exact (ht.coherent hi.forest.2.2.2 hi.forest.2.2.1 hi.below hi.nodup6 hi.lists.swap).swap
    · exact (ht.owners hi.valid6 ha hc hi.owners.swap hpid).swap
  · have ht : Inserted d out true t4 t6 addr cidr pid := h
    refine ⟨⟨ht.root, ?_, ht.rep, ht.otherRep⟩,
      Tree.insertFresh_valid hi.valid4 ha hc d.nextNode pid, hi.valid6,
      Tree.insertFresh_compressed hi.compressed4 32 d.nextNode addr cidr pid, hi.compressed6,
      Tree.insertFresh_nodeIds_nodup hi.nodup4 (hi.forest.2.2.1.ids_below hi.below) 32 addr cidr pid, hi.nodup6,
      ht.below, ht.coherent hi.forest.2.2.1 hi.forest.2.2.2 hi.below hi.nodup4 hi.lists,
      ht.owners hi.valid4 ha hc hi.owners hpid, ht.peerSlots hi.peerSlots⟩
    exact ht.otherRoot.trans hi.forest.2.1

theorem RoutingInvariant.bumpSeq (hi : RoutingInvariant d t4 t6) :
    RoutingInvariant (bumpSeq d) t4 t6 :=
  ⟨hi.forest, hi.valid4, hi.valid6, hi.compressed4, hi.compressed6,
    hi.nodup4, hi.nodup6, hi.below, hi.lists, hi.owners, hi.peerSlots⟩

/-- Coherence makes rollback's fresh-ID filtering inert pointwise, but the
allocation frontier still advances once. No whole-Device equality is claimed. -/
theorem RoutingInvariant.rollback_peers (hi : RoutingInvariant d t4 t6)
    (width addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p) (q : Nat) :
    (graftRolledBack d width addr cidr pid p).peers[q]? = d.peers[q]? := by
  rw [graftRolledBack_peer d width addr cidr pid p hp]
  cases hq : d.peers[q]? with
  | none => rfl
  | some old =>
    have hn : d.nextNode ∉ old.allowedipsList := by
      intro hm
      exact Nat.lt_irrefl _ (resident_list_ids_below hi.lists hi.forest.2.2.1 hi.forest.2.2.2 hi.below hq hm)
    simp only [Option.map_some, unlist_of_absent old d.nextNode hn]

theorem RoutingInvariant.rollback (hi : RoutingInvariant d t4 t6)
    (width addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p) :
    RoutingInvariant (graftRolledBack d width addr cidr pid p) t4 t6 := by
  have hm := hi.rollback_peers width addr cidr pid p hp
  have hf : ForestRep (graftRolledBack d width addr cidr pid p) t4 t6 := by
    refine ⟨?_, ?_,
      graftRolledBack_rep d width addr cidr pid p hi.below t4 32 .root4 hi.forest.2.2.1,
      graftRolledBack_rep d width addr cidr pid p hi.below t6 128 .root6 hi.forest.2.2.2⟩
    · simpa only [graftRolledBack, unlisted, graftListed, allocated] using hi.forest.1
    · simpa only [graftRolledBack, unlisted, graftListed, allocated] using hi.forest.2.1
  have hn : (graftRolledBack d width addr cidr pid p).nextPeer = d.nextPeer := by
    simp only [graftRolledBack, unlisted, graftListed, allocated]
  refine {
    forest := hf
    valid4 := hi.valid4
    valid6 := hi.valid6
    compressed4 := hi.compressed4
    compressed6 := hi.compressed6
    nodup4 := hi.nodup4
    nodup6 := hi.nodup6
    below := graftRolledBack_below d width addr cidr pid p hi.below
    lists := ?_
    owners := ?_
    peerSlots := ?_ }
  · intro q old hq
    exact hi.lists q old ((hm q) ▸ hq)
  · intro e he
    rw [hn]
    exact hi.owners e he
  · intro q old hq
    rw [hn]
    exact hi.peerSlots q old ((hm q) ▸ hq)

theorem RoutingInvariant.removed (hi : RoutingInvariant d t4 t6)
    (h : RemovedPeer d out t4 t6 pid saved) :
    RoutingInvariant out (t4.eraseIds saved) (t6.eraseIds saved) := by
  have hnext : out.nextPeer = d.nextPeer := by
    have he := congrArg WG.Device.nextPeer h.frame
    exact he
  refine ⟨h.loop.forest, Tree.eraseIds_valid t4 saved hi.valid4, Tree.eraseIds_valid t6 saved hi.valid6,
    Tree.eraseIds_compressed t4 saved hi.compressed4, Tree.eraseIds_compressed t6 saved hi.compressed6,
    (Tree.eraseIds_nodeIds t4 saved).nodup hi.nodup4, (Tree.eraseIds_nodeIds t6 saved).nodup hi.nodup6,
    h.below hi.below, h.coherent, ?_, ?_⟩
  · intro e he
    rw [hnext]
    rw [h.entries] at he
    exact hi.owners e (List.mem_filter.mp he).1
  · intro q p hp
    rw [h.peers] at hp
    obtain ⟨old, hold, _⟩ := Option.map_eq_some_iff.mp hp
    rw [hnext]
    exact hi.peerSlots q old hold

end Leanux.Proofs.WG.AllowedIps
