import Leanux.Proofs.WG.AllowedIps.GraftMirror

/-! Store consequences of selected-root grafting. Rollback restores node
lookups under whole-store freshness; peer values retain the source filtering. -/
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Std.Do Leanux.Proofs.Framing

/-- Change only the root backlink while framing all descendant records. -/
theorem RepAt.root_reparent {nodes nodes' : Std.TreeMap Nat WG.AipNode}
    {width : Nat} {base base' : WG.Slot} {n : NodeData} {l r : Tree}
    (hr : RepAt nodes width base (.node n l r))
    (hn : nodes'[n.id]? = some (encode width base' n l r))
    (hf : ∀ id ∈ l.nodeIds ++ r.nodeIds, nodes'[id]? = nodes[id]?) :
    RepAt nodes' width base' (.node n l r) :=
  ⟨hn, hr.2.1.congr (fun id hi => hf id (List.mem_append_left _ hi)),
    hr.2.2.congr (fun id hi => hf id (List.mem_append_right _ hi))⟩

theorem graftRolledBack_node (d : WG.Device) (width addr cidr pid : Nat) (p : WG.Peer) (id : Nat) :
    (graftRolledBack d width addr cidr pid p).nodes[id]? =
      if id = d.nextNode then none else d.nodes[id]? := by
  by_cases hi : id = d.nextNode
  · subst id
    simp [graftRolledBack, unlisted, graftListed, allocated]
  · simp [graftRolledBack, unlisted, graftListed, allocated, Std.TreeMap.getElem?_erase,
      Std.TreeMap.getElem?_insert, hi, Ne.symm hi]

theorem graftRolledBack_nodes (d : WG.Device) (width addr cidr pid : Nat) (p : WG.Peer)
    (hb : NodesBelow d) (id : Nat) :
    (graftRolledBack d width addr cidr pid p).nodes[id]? = d.nodes[id]? := by
  rw [graftRolledBack_node]
  split
  · rename_i he
    subst id
    cases hn : d.nodes[d.nextNode]? with
    | none => rfl
    | some n => exact False.elim ((Nat.lt_irrefl _) (hb d.nextNode n hn))
  · rfl

theorem graftRolledBack_peer (d : WG.Device) (width addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (q : Nat) :
    (graftRolledBack d width addr cidr pid p).peers[q]? = (d.peers[q]?).map (unlist d.nextNode) := by
  change (unlisted (graftListed d width addr cidr pid p) d.nextNode).peers[q]? = _
  rw [unlisted_get]
  by_cases he : pid = q
  · subst q
    simp [graftListed, allocated, hp, unlist, WG.listRemove, List.filter_append]
  · simp [graftListed, allocated, Std.TreeMap.getElem?_insert, he]

theorem graftRolledBack_below (d : WG.Device) (width addr cidr pid : Nat) (p : WG.Peer)
    (hb : NodesBelow d) : NodesBelow (graftRolledBack d width addr cidr pid p) := by
  intro id n hn
  rw [graftRolledBack_nodes d width addr cidr pid p hb] at hn
  exact Nat.lt_trans (hb id n hn) (Nat.lt_succ_self _)

theorem graftRolledBack_rep (d : WG.Device) (width addr cidr pid : Nat) (p : WG.Peer)
    (hb : NodesBelow d) (t : Tree) (family : Nat) (base : WG.Slot)
    (hr : RepAt d.nodes family base t) :
    RepAt (graftRolledBack d width addr cidr pid p).nodes family base t :=
  hr.congr (fun id _ => graftRolledBack_nodes d width addr cidr pid p hb id)

theorem add_root_graft_wp (k : Kernel) (d : WG.Device) (hd : k.wg = some d)
    (v4 : Bool) (n : NodeData) (l r : Tree) (addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (hroot : rootValue d v4 = some n.id)
    (hb : NodesBelow d) (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (.node n l r))
    (hv : (Tree.node n l r).Valid (rootWidth v4)) (ha : addr < 2 ^ rootWidth v4)
    (hc : cidr ≤ rootWidth v4)
    (hstop : ¬ (n.cidr ≤ cidr ∧ prefixBits (rootWidth v4) n.cidr n.addr = prefixBits (rootWidth v4) n.cidr addr)) :
    ⦃fun w => ⌜w.k = k⌝⦄ WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)
    ⦃⇓? result w => ⌜(result = -ENOMEM ∧ w.k = k) ∨
      (result = -ENOMEM ∧ min cidr (common (rootWidth v4) n.addr addr) ≠ cidr ∧
        w.k = { k with wg := some (graftRolledBack d (rootWidth v4) addr cidr pid p) }) ∨
      (result = 0 ∧ w.k = { k with wg := some (graftInstalled d v4 n.id
        (encode (rootWidth v4) (rootSlot v4) n l r) addr cidr pid p) })⌝⦄ := by
  have hw : rootWidth v4 = 32 ∨ rootWidth v4 = 128 := by cases v4 <;> simp [rootWidth]
  have placement := nodePlacement_root_stopped_wp k d hd (rootWidth v4) addr cidr hw ha hc
    (rootSlot v4) n l r hr hv hstop
  have hg := graftable_of_stopped hv ha hstop
  have bound : min cidr (common (rootWidth v4) n.addr addr) < rootWidth v4 :=
    Nat.lt_of_lt_of_le hg hv.2.1
  exact add_placed_root_graft_wp k d hd v4 n.id
    (encode (rootWidth v4) (rootSlot v4) n l r) addr cidr pid p hp hr.1 hroot
    (hb n.id _ hr.1) hc bound placement

theorem graftOne_nodes_other (d : WG.Device) (v4 : Bool) (id : Nat) (old : WG.AipNode)
    (addr cidr pid : Nat) (p : WG.Peer) (q : Nat) (hf : d.nextNode ≠ q) (ho : id ≠ q) :
    (graftOne d v4 id old addr cidr pid p).nodes[q]? = d.nodes[q]? := by
  simp [graftOne, connectedRoot, rootWrite, connectedChild, graftListed, allocated,
    Std.TreeMap.getElem?_insert, hf, ho]

theorem graftTwo_nodes_other (d : WG.Device) (v4 : Bool) (id : Nat) (old : WG.AipNode)
    (addr cidr pid split : Nat) (p : WG.Peer) (q : Nat)
    (hf : d.nextNode ≠ q) (hm : d.nextNode + 1 ≠ q) (ho : id ≠ q) :
    (graftTwo d v4 id old addr cidr pid split p).nodes[q]? = d.nodes[q]? := by
  simp [graftTwo, connectedRoot, rootWrite, connectedChild, graftListed, allocated,
    Std.TreeMap.getElem?_insert, hf, hm, ho]

theorem graftInstalled_metadata (d : WG.Device) (v4 : Bool) (id : Nat) (old : WG.AipNode)
    (addr cidr pid : Nat) (p : WG.Peer) :
    let split := min cidr (common (rootWidth v4) old.bits addr)
    let installed := graftInstalled d v4 id old addr cidr pid p
    installed.nextNode = d.nextNode + (if split = cidr then 1 else 2) ∧
      rootValue installed v4 = some (if split = cidr then d.nextNode else d.nextNode + 1) ∧
      rootValue installed (!v4) = rootValue d (!v4) ∧
      installed.peerAllowedips.seq = d.peerAllowedips.seq := by
  dsimp only
  unfold graftInstalled
  split <;> cases v4 <;> simp_all [graftOne, graftTwo, connectedRoot, rootWrite,
    connectedChild, graftListed, allocated, rootValue, rootWidth]

end Leanux.Proofs.WG.AllowedIps
