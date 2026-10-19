import Leanux.Proofs.WG.AllowedIps.RoutingInvariant

/-! Conditional preservation through the original insertion wrapper, including
both normal allocation refusals. This layer assumes coherent represented input;
it does not establish that input from a configuration or runner history. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux
set_option pp.structureInstances false

theorem RoutingInvariant.selected_root (h : RoutingInvariant d t4 t6) (v4 : Bool) :
    rootValue d v4 = (selectedTree v4 t4 t6).root := by
  cases v4
  · exact h.forest.2.1
  · exact h.forest.1

theorem RoutingInvariant.selected_rep (h : RoutingInvariant d t4 t6) (v4 : Bool) :
    RepAt d.nodes (rootWidth v4) (rootSlot v4) (selectedTree v4 t4 t6) := by
  cases v4
  · exact h.forest.2.2.2
  · exact h.forest.2.2.1

theorem RoutingInvariant.selected_valid (h : RoutingInvariant d t4 t6) (v4 : Bool) :
    (selectedTree v4 t4 t6).Valid (rootWidth v4) := by
  cases v4
  · exact h.valid6
  · exact h.valid4

theorem RoutingInvariant.selected_nodup (h : RoutingInvariant d t4 t6) (v4 : Bool) :
    (selectedTree v4 t4 t6).nodeIds.Nodup := by
  cases v4
  · exact h.nodup6
  · exact h.nodup4

theorem insertionFrame_bump (h : InsertionFrame (bumpSeq d) out) : InsertionFrame d out := by
  simpa only [InsertionFrame, bumpSeq] using h

theorem graftRolledBack_frame (d : WG.Device) (width addr cidr pid : Nat) (p : WG.Peer) :
    InsertionFrame d (graftRolledBack d width addr cidr pid p) := by
  simp only [InsertionFrame, graftRolledBack, unlisted, graftListed, allocated]

/-- Every normal refusal preserves represented node/list contents pointwise,
while the wrapper increments sequence and a partial graft may consume one ID.
This is deliberately not a transaction-rollback or a failed-Stop state claim. -/
structure InsertRefused (d out : WG.Device) (t4 t6 : Tree) : Prop where
  invariant : RoutingInvariant out t4 t6
  nodes : ∀ id : Nat, out.nodes[id]? = d.nodes[id]?
  peers : ∀ pid : Nat, out.peers[pid]? = d.peers[pid]?
  trie : out.peerAllowedips = {d.peerAllowedips with seq := d.peerAllowedips.seq + 1}
  frontier : out.nextNode = d.nextNode ∨ out.nextNode = d.nextNode + 1

/-- Common full-device frame and sequence effect, followed by the actual normal
return split. Success retains the source-derived raw peer-map effect as well as
coherent output; refusal retains exact pointwise stores and the burned frontier. -/
structure InsertRoutingOutcome (d out : WG.Device) (v4 : Bool) (t4 t6 : Tree)
    (addr cidr pid : Nat) (ret : Int) : Prop where
  frame : InsertionFrame d out
  seq : out.peerAllowedips.seq = d.peerAllowedips.seq + 1
  result :
    (ret = 0 ∧
      Inserted (bumpSeq d) out v4 (selectedTree v4 t4 t6) (selectedTree (!v4) t4 t6) addr cidr pid ∧
      RoutingInvariant out (insertedTree4 d v4 t4 addr cidr pid) (insertedTree6 d v4 t6 addr cidr pid)) ∨
    (ret = -ENOMEM ∧ InsertRefused d out t4 t6)

theorem insert_routing_outcome (w w' : WGWorld) (ambient ambient' : Ambient) (d : WG.Device) (hd : w.dev = some d)
    (family addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (t4 t6 : Tree) (hi : RoutingInvariant d t4 t6)
    (ha : addr < 2 ^ rootWidth (family == 4)) (hc : cidr ≤ rootWidth (family == 4))
    (ret : Int) (hrun : ((WG.insert family addr cidr pid).run w).run ambient = .ok ((ret, w'), ambient')) :
    ∃ out, w' = {w with dev := some out} ∧
      InsertRoutingOutcome d out (family == 4) t4 t6 addr cidr pid ret := by
  have ho := insert_outcome w w' ambient ambient' d hd family (selectedTree (family == 4) t4 t6)
    (selectedTree (!(family == 4)) t4 t6) addr cidr pid p hp (hi.selected_root _)
    hi.below (hi.selected_rep _) (hi.selected_valid _) (hi.selected_nodup _) ha hc
    (hi.selected_rep _) ret hrun
  rcases ho with ⟨hr, hk⟩ | ⟨hr, _, hk⟩ | ⟨hr, out, hk, hs⟩
  · refine ⟨bumpSeq d, hk, ?_, rfl, .inr ⟨hr, hi.bumpSeq, ?_, ?_, rfl, .inl rfl⟩⟩
    · simp only [InsertionFrame, bumpSeq]
    · intro id; rfl
    · intro q; rfl
  · let out := graftRolledBack (bumpSeq d) (rootWidth (family == 4)) addr cidr pid p
    have hi' := hi.bumpSeq.rollback (rootWidth (family == 4)) addr cidr pid p hp
    refine ⟨out, hk, insertionFrame_bump (graftRolledBack_frame ..), ?_, .inr ⟨hr, hi', ?_, ?_, ?_, .inr ?_⟩⟩
    · simp only [out, graftRolledBack, unlisted, graftListed, allocated, bumpSeq]
    · exact graftRolledBack_nodes (bumpSeq d) (rootWidth (family == 4)) addr cidr pid p hi.bumpSeq.below
    · exact hi.bumpSeq.rollback_peers (rootWidth (family == 4)) addr cidr pid p hp
    · simp only [out, graftRolledBack, unlisted, graftListed, allocated, bumpSeq]
    · simp only [out, graftRolledBack, unlisted, graftListed, allocated, bumpSeq]
  · exact ⟨out, hk, insertionFrame_bump hs.frame, hs.seq,
      .inl ⟨hr, hs, hi.bumpSeq.inserted (family == 4) addr cidr pid p hp ha hc hs⟩⟩

theorem RoutingInvariant.selected_lists (h : RoutingInvariant d t4 t6) (v4 : Bool) :
    ResidentLists d (selectedTree v4 t4 t6) (selectedTree (!v4) t4 t6) := by
  cases v4
  · exact h.lists.swap
  · exact h.lists

/-- Successful original insertion has both its raw source peer-map equation
and, under coherent input, the normalized all-peer move-to-tail equation. -/
theorem insert_routing_success (w w' : WGWorld) (ambient ambient' : Ambient) (d : WG.Device) (hd : w.dev = some d)
    (family addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (t4 t6 : Tree) (hi : RoutingInvariant d t4 t6)
    (ha : addr < 2 ^ rootWidth (family == 4)) (hc : cidr ≤ rootWidth (family == 4))
    (hrun : ((WG.insert family addr cidr pid).run w).run ambient = .ok ((0, w'), ambient')) :
    let v4 := family == 4
    let inserted := (selectedTree v4 t4 t6).insertFresh (rootWidth v4) d.nextNode addr cidr pid
    ∃ out, w' = {w with dev := some out} ∧
      InsertRoutingOutcome d out v4 t4 t6 addr cidr pid 0 ∧
      RoutingInvariant out (insertedTree4 d v4 t4 addr cidr pid) (insertedTree6 d v4 t6 addr cidr pid) ∧
      InsertionPeers d out inserted.allocations inserted.binding.id pid ∧
      (∀ q : Nat, out.peers[q]? = (d.peers[q]?).map (insertionPeer 0 inserted.binding.id pid q)) := by
  obtain ⟨out, hk, ho⟩ := insert_routing_outcome w w' ambient ambient' d hd family addr cidr pid p hp t4 t6 hi ha hc 0 hrun
  rcases ho.result with ⟨_, hs, hinv⟩ | ⟨hf, _⟩
  · exact ⟨out, hk, ho, hinv, hs.peers,
      hs.normalized_peers (hi.bumpSeq.selected_rep _) (hi.bumpSeq.selected_rep _)
        hi.bumpSeq.below (hi.bumpSeq.selected_lists _)⟩
  · simp [ENOMEM] at hf

/-- Normal ENOMEM keeps the coherent pointwise stores and original trees,
with the wrapper sequence bump and the exact zero-or-one consumed-ID bound. -/
theorem insert_routing_refusal (w w' : WGWorld) (ambient ambient' : Ambient) (d : WG.Device) (hd : w.dev = some d)
    (family addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (t4 t6 : Tree) (hi : RoutingInvariant d t4 t6)
    (ha : addr < 2 ^ rootWidth (family == 4)) (hc : cidr ≤ rootWidth (family == 4))
    (hrun : ((WG.insert family addr cidr pid).run w).run ambient = .ok ((-ENOMEM, w'), ambient')) :
    ∃ out, w' = {w with dev := some out} ∧ InsertionFrame d out ∧ InsertRefused d out t4 t6 := by
  obtain ⟨out, hk, ho⟩ := insert_routing_outcome w w' ambient ambient' d hd family addr cidr pid p hp t4 t6 hi ha hc (-ENOMEM) hrun
  rcases ho.result with ⟨hf, _⟩ | ⟨_, hs⟩
  · simp [ENOMEM] at hf
  · exact ⟨out, hk, ho.frame, hs⟩

/-- Complete original removal preserves the same invariant from a resident
peer. Its saved list and precise filtering effects remain in RemovedPeer. -/
theorem removeByPeer_routing_total (w : WGWorld) (ambient : Ambient) (d : WG.Device) (hd : w.dev = some d)
    (pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (t4 t6 : Tree) (hi : RoutingInvariant d t4 t6) :
    ∃ out w' ambient', ((WG.removeByPeer pid).run w).run ambient = .ok (((), w'), ambient') ∧
      w' = {w with dev := some out} ∧ RemovedPeer d out t4 t6 pid p.allowedipsList ∧
      RoutingInvariant out (t4.eraseIds p.allowedipsList) (t6.eraseIds p.allowedipsList) := by
  obtain ⟨out, w', ambient', he, hk, hs⟩ := removeByPeer_total w ambient d hd pid p hp t4 t6 hi.forest
    hi.nodup4 hi.nodup6 hi.compressed4 hi.compressed6 hi.lists
  exact ⟨out, w', ambient', he, hk, hs, hi.removed hs⟩

end Leanux.Proofs.WG.AllowedIps
