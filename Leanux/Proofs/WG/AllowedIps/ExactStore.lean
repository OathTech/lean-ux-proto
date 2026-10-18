import Leanux.Proofs.WG.AllowedIps.ExactMutation

/-! Structural consequences of exact-prefix replacement. Duplicate-free
represented identifiers protect descendants, ancestors and siblings. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux

theorem context_exact_insertFresh (c : Context) (n : NodeData) (l r : Tree)
    (width fresh addr cidr pid : Nat) (hf : c.Follows width addr cidr) (hn : n.cidr = cidr)
    (hm : prefixBits width n.cidr n.addr = prefixBits width n.cidr addr) :
    (c.plug (.node n l r)).insertFresh width fresh addr cidr pid =
      ⟨c.plug (.node { n with peer := some pid } l r), n.entry pid, 0⟩ := by
  rw [c.insertFresh _ fresh pid hf]
  rw [hn] at hm
  simp [Tree.insertFresh, hn, hm]

theorem exactInstalled_nodes_other (d : WG.Device) (id : Nat) (old : WG.AipNode)
    (pid : Nat) (p : WG.Peer) (j : Nat) (hne : id ≠ j) :
    (exactInstalled d id old pid p).nodes[j]? = d.nodes[j]? := by
  simp [exactInstalled, Std.TreeMap.getElem?_insert, hne]

theorem exactInstalled_below (d : WG.Device) (id : Nat) (old : WG.AipNode)
    (pid : Nat) (p : WG.Peer) (hb : NodesBelow d) (hi : id < d.nextNode) :
    NodesBelow (exactInstalled d id old pid p) := by
  intro j node hget
  change j < d.nextNode
  by_cases he : id = j
  · exact he ▸ hi
  · rw [exactInstalled_nodes_other d id old pid p j he] at hget
    exact hb j node hget

theorem exactInstalled_rep (d : WG.Device) (width : Nat) (base : WG.Slot)
    (n : NodeData) (l r : Tree) (pid : Nat) (p : WG.Peer)
    (hr : RepAt d.nodes width base (.node n l r)) (hn : (Tree.node n l r).nodeIds.Nodup) :
    RepAt (exactInstalled d n.id (encode width base n l r) pid p).nodes width base
      (.node { n with peer := some pid } l r) := by
  have hnot := (List.nodup_cons.mp hn).1
  refine ⟨?_, ?_, ?_⟩
  · simp [exactInstalled, encode]
  · apply hr.2.1.congr
    intro id hi
    exact exactInstalled_nodes_other d n.id _ pid p id
      (fun he => hnot (List.mem_append_left _ (he ▸ hi)))
  · apply hr.2.2.congr
    intro id hi
    exact exactInstalled_nodes_other d n.id _ pid p id
      (fun he => hnot (List.mem_append_right _ (he ▸ hi)))

theorem exactInstalled_context_rep (d : WG.Device) (width : Nat) (base : WG.Slot)
    (c : Context) (n : NodeData) (l r : Tree) (pid : Nat) (p : WG.Peer)
    (hr : RepAt d.nodes width base (c.plug (.node n l r)))
    (hn : (c.plug (.node n l r)).nodeIds.Nodup) :
    RepAt (exactInstalled d n.id (encode width (c.slot base) n l r) pid p).nodes width base
      (c.plug (.node { n with peer := some pid } l r)) := by
  apply c.rep_replace_sameRoot _ _ _ hr
    (exactInstalled_rep d width (c.slot base) n l r pid p (c.focus_rep _ _ hr) (c.focus_nodup _ hn)) rfl
  intro id hi
  have hnot := c.focus_disjoint _ hn n.id (by simp [Tree.nodeIds])
  exact exactInstalled_nodes_other d n.id _ pid p id (fun he => hnot (he ▸ hi))

theorem exactInstalled_other_rep (d : WG.Device) (v4 : Bool) (base : WG.Slot)
    (n : NodeData) (l r : Tree) (pid : Nat) (p : WG.Peer)
    (hr : RepAt d.nodes (rootWidth v4) base (.node n l r)) (other : Tree)
    (ho : RepAt d.nodes (rootWidth (!v4)) (rootSlot (!v4)) other) :
    RepAt (exactInstalled d n.id (encode (rootWidth v4) base n l r) pid p).nodes
      (rootWidth (!v4)) (rootSlot (!v4)) other := by
  apply ho.congr
  intro id hi
  apply exactInstalled_nodes_other
  intro he
  subst id
  obtain ⟨node, hn, hw⟩ := ho.resident_bitlen hi
  have heq := Option.some.inj (hn.symm.trans hr.1)
  rw [heq] at hw
  cases v4 <;> simp [encode, rootWidth] at hw

theorem exactInstalled_peer (d : WG.Device) (id : Nat) (old : WG.AipNode)
    (pid : Nat) (p : WG.Peer) :
    (exactInstalled d id old pid p).peers[pid]? =
      some { p with allowedipsList := WG.listRemove p.allowedipsList id ++ [id] } := by
  simp [exactInstalled, unlist]

theorem exactInstalled_other_peer (d : WG.Device) (id : Nat) (old : WG.AipNode)
    (pid : Nat) (p : WG.Peer) (other : Nat) (hn : pid ≠ other) :
    (exactInstalled d id old pid p).peers[other]? = (d.peers[other]?).map (unlist id) := by
  simp [exactInstalled, Std.TreeMap.getElem?_insert, hn, unlisted_get]

theorem Context.nodeIds_congr (c : Context) {before after : Tree}
    (h : after.nodeIds = before.nodeIds) : (c.plug after).nodeIds = (c.plug before).nodeIds := by
  induction c <;> simp_all [Context.plug, Tree.nodeIds]

theorem exactInstalled_identity (d : WG.Device) (id : Nat) (old : WG.AipNode)
    (pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p) (q : Nat) :
    ((exactInstalled d id old pid p).peers[q]?).map WG.Peer.internalId =
      (d.peers[q]?).map WG.Peer.internalId := by
  by_cases he : pid = q
  · subst q
    rw [exactInstalled_peer, hp]
    rfl
  · rw [exactInstalled_other_peer d id old pid p q he]
    cases d.peers[q]? <;> rfl

end Leanux.Proofs.WG.AllowedIps
