import Leanux.Proofs.WG.AllowedIps.RemovalContext

/-! Local represented endpoints for the original nonroot mutations.
Every separation premise below is extracted from the input tree's Nodup. -/
set_option maxHeartbeats 1000000
namespace Leanux.Proofs.WG.AllowedIps
open Leanux

theorem removalChildUnary_rep (d : WG.Device) (width : Nat) (base : WG.Slot)
    (p n c : NodeData) (side childSide : Nat) (l r sibling : Tree)
    (hb : side < 2) (hcb : childSide < 2)
    (hr : RepAt d.nodes width base
      (Tree.fork p side (Tree.fork n childSide (.node c l r) .empty) sibling))
    (hn : (Tree.fork p side (Tree.fork n childSide (.node c l r) .empty) sibling).nodeIds.Nodup) :
    let old := Tree.fork n childSide (.node c l r) .empty
    let out := removalChildUnary d n.id
      (forkNode width (.child p.id side) n childSide (.node c l r) .empty)
      p.id side (forkNode width base p side old sibling) c.id
      (encode width (.child n.id childSide) c l r)
    RepAt out.nodes width base (Tree.fork p side (.node c l r) sibling) := by
  dsimp only
  obtain ⟨hp, ht, hs⟩ := fork_rep_parts hb hr
  obtain ⟨htn, hc, _⟩ := fork_rep_parts hcb ht
  obtain ⟨hpt, hps, hnt, _, hts⟩ := (Tree.fork_nodup_iff ..).mp hn
  obtain ⟨hnc, _, hncdup, _, _⟩ := (Tree.fork_nodup_iff ..).mp hnt
  have hpc : p.id ≠ c.id := fun he => hpt (by simp [Tree.mem_fork_nodeIds, Tree.nodeIds, he])
  have hpn : p.id ≠ n.id := fun he => hpt (by simp [Tree.mem_fork_nodeIds, he])
  have hnc' : n.id ≠ c.id := fun he => hnc (by simp [Tree.nodeIds, he])
  have hcd := (List.nodup_cons.mp hncdup).1
  apply fork_rep_intro hb
  · rw [removalChildUnary_node]
    simp only [Ne.symm hpn, ↓reduceIte, ite_true]
    exact congrArg some (forkNode_replace (after := .node c l r) hb)
  · apply hc.root_reparent
    · simp [removalChildUnary_node, hnc', hpc, encode]
    · intro q hq
      have hin : q ∈ (Tree.node c l r).nodeIds := by simp [Tree.nodeIds, hq]
      have hntq : n.id ≠ q := fun he => hnc (he ▸ hin)
      have hptq : p.id ≠ q := fun he => hpt (by simp [Tree.mem_fork_nodeIds, he, hin])
      have hctq : c.id ≠ q := fun he => hcd (he ▸ hq)
      simp [removalChildUnary_node, hntq, hptq, hctq]
  · apply hs.congr
    intro q hq
    have hpq : p.id ≠ q := fun he => hps (he ▸ hq)
    have hnq : n.id ≠ q := fun he => hts n.id (by simp [Tree.mem_fork_nodeIds]) (he ▸ hq)
    have hcq : c.id ≠ q := fun he => hts c.id
      (by simp [Tree.mem_fork_nodeIds, Tree.nodeIds]) (he ▸ hq)
    simp [removalChildUnary_node, hpq, hnq, hcq]

theorem removalLeafDetached_rep (d : WG.Device) (width : Nat) (base : WG.Slot)
    (p n : NodeData) (side : Nat) (sibling : Tree) (hb : side < 2)
    (hr : RepAt d.nodes width base (Tree.fork p side (.node n .empty .empty) sibling))
    (hn : (Tree.fork p side (.node n .empty .empty) sibling).nodeIds.Nodup) :
    RepAt (removalLeafDetached d n.id (encode width (.child p.id side) n .empty .empty)
      p.id side (forkNode width base p side (.node n .empty .empty) sibling)).nodes
      width base (Tree.fork p side .empty sibling) := by
  obtain ⟨hp, ht, hs⟩ := fork_rep_parts hb hr
  obtain ⟨hpt, hps, _, _, hts⟩ := (Tree.fork_nodup_iff ..).mp hn
  have hnp : n.id ≠ p.id := fun he => hpt (by simp [Tree.nodeIds, he])
  apply fork_rep_intro hb
  · rw [removalLeafDetached_node]
    simp only [hnp, ↓reduceIte, ite_true]
    exact congrArg some (forkNode_replace (after := .empty) hb)
  · trivial
  · apply hs.congr
    intro q hq
    have hpq : p.id ≠ q := fun he => hps (he ▸ hq)
    have hnq : n.id ≠ q := fun he => hts n.id (by simp [Tree.nodeIds]) (he ▸ hq)
    simp [removalLeafDetached_node, hpq, hnq]

theorem removalCollapseRoot_rep (d : WG.Device) (v4 : Bool) (p n c : NodeData)
    (side : Nat) (l r : Tree) (hb : side < 2)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4)
      (Tree.fork p side (.node n .empty .empty) (.node c l r)))
    (hn : (Tree.fork p side (.node n .empty .empty) (.node c l r)).nodeIds.Nodup) :
    RepAt (removalCollapseRoot d n.id
      (encode (rootWidth v4) (.child p.id side) n .empty .empty) p.id side
      (forkNode (rootWidth v4) (rootSlot v4) p side (.node n .empty .empty) (.node c l r))
      v4 (some (c.id, encode (rootWidth v4) (.child p.id (1-side)) c l r))).nodes
      (rootWidth v4) (rootSlot v4) (.node c l r) := by
  obtain ⟨hp, ht, hs⟩ := fork_rep_parts hb hr
  obtain ⟨hpt, hps, _, hcs, hts⟩ := (Tree.fork_nodup_iff ..).mp hn
  have hpc : p.id ≠ c.id := fun he => hps (by simp [Tree.nodeIds, he])
  have hcd := (List.nodup_cons.mp hcs).1
  apply hs.root_reparent
  · simp [removalCollapseRoot_node, hpc, encode]
  · intro q hq
    have hsin : q ∈ (Tree.node c l r).nodeIds := by simp [Tree.nodeIds, hq]
    have hpq : p.id ≠ q := fun he => hps (he ▸ hsin)
    have hnq : n.id ≠ q := fun he => hts n.id (by simp [Tree.nodeIds]) (he ▸ hsin)
    have hcq : c.id ≠ q := fun he => hcd (he ▸ hq)
    simp [removalCollapseRoot_node, hpq, hnq, hcq]

theorem removalCollapseChild_rep (d : WG.Device) (width : Nat) (base : WG.Slot)
    (g p n c : NodeData) (gside side : Nat) (l r outerSibling : Tree)
    (hgb : gside < 2) (hb : side < 2)
    (hr : RepAt d.nodes width base (Tree.fork g gside
      (Tree.fork p side (.node n .empty .empty) (.node c l r)) outerSibling))
    (hn : (Tree.fork g gside
      (Tree.fork p side (.node n .empty .empty) (.node c l r)) outerSibling).nodeIds.Nodup) :
    let old := Tree.fork p side (.node n .empty .empty) (.node c l r)
    RepAt (removalCollapseChild d n.id
      (encode width (.child p.id side) n .empty .empty) p.id side
      (forkNode width (.child g.id gside) p side (.node n .empty .empty) (.node c l r))
      g.id gside (forkNode width base g gside old outerSibling)
      (some (c.id, encode width (.child p.id (1-side)) c l r))).nodes
      width base (Tree.fork g gside (.node c l r) outerSibling) := by
  dsimp only
  obtain ⟨hg, hp, hos⟩ := fork_rep_parts hgb hr
  obtain ⟨hpn, ht, hs⟩ := fork_rep_parts hb hp
  obtain ⟨hgp, hgos, hpdup, _, hpos⟩ := (Tree.fork_nodup_iff ..).mp hn
  obtain ⟨hpt, hps, _, hcs, hts⟩ := (Tree.fork_nodup_iff ..).mp hpdup
  have hpg : p.id ≠ g.id := fun he => hgp (by simp [Tree.mem_fork_nodeIds, he])
  have hpc : p.id ≠ c.id := fun he => hps (by simp [Tree.nodeIds, he])
  have hgc : g.id ≠ c.id := fun he => hgp (by simp [Tree.mem_fork_nodeIds, Tree.nodeIds, he])
  have hcd := (List.nodup_cons.mp hcs).1
  apply fork_rep_intro hgb
  · rw [removalCollapseChild_node]
    simp only [hpg, ↓reduceIte, ite_true, Option.map_some]
    exact congrArg some (forkNode_replace (after := .node c l r) hgb)
  · apply hs.root_reparent
    · simp [removalCollapseChild_node, hpc, hgc, encode]
    · intro q hq
      have hsin : q ∈ (Tree.node c l r).nodeIds := by simp [Tree.nodeIds, hq]
      have hpq : p.id ≠ q := fun he => hps (he ▸ hsin)
      have hgq : g.id ≠ q := fun he => hgp (by simp [Tree.mem_fork_nodeIds, he, hsin])
      have hnq : n.id ≠ q := fun he => hts n.id (by simp [Tree.nodeIds]) (he ▸ hsin)
      have hcq : c.id ≠ q := fun he => hcd (he ▸ hq)
      simp [removalCollapseChild_node, hpq, hgq, hnq, hcq]
  · apply hos.congr
    intro q hq
    have hgq : g.id ≠ q := fun he => hgos (he ▸ hq)
    have hpq : p.id ≠ q := fun he => hpos p.id (by simp [Tree.mem_fork_nodeIds]) (he ▸ hq)
    have hnq : n.id ≠ q := fun he => hpos n.id
      (by simp [Tree.mem_fork_nodeIds, Tree.nodeIds]) (he ▸ hq)
    have hcq : c.id ≠ q := fun he => hpos c.id
      (by simp [Tree.mem_fork_nodeIds, Tree.nodeIds]) (he ▸ hq)
    simp [removalCollapseChild_node, hpq, hgq, hnq, hcq]

end Leanux.Proofs.WG.AllowedIps
