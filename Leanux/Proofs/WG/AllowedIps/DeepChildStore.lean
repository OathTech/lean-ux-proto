import Leanux.Proofs.WG.AllowedIps.DeepChild

/-! Store representation for empty-child insertion beneath a context.
Global node freshness and duplicate-free represented identifiers protect
all ancestors and siblings from the two changed node-map entries. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux

theorem gapInstalledAt_nodes_other (d : WG.Device) (v4 : Bool) (base : WG.Slot) (n : NodeData)
    (side : Nat) (sibling : Tree) (addr cidr pid : Nat) (p : WG.Peer)
    (id : Nat) (hf : d.nextNode ≠ id) (hp : n.id ≠ id) :
    (gapInstalledAt d v4 base n side sibling addr cidr pid p).nodes[id]? = d.nodes[id]? := by
  simp [gapInstalledAt, connectedChild, allocated, Std.TreeMap.getElem?_insert, hf, hp]

theorem gapInstalledAt_rep (d : WG.Device) (v4 : Bool) (base : WG.Slot) (n : NodeData)
    (side : Nat) (sibling : Tree) (addr cidr pid : Nat) (p : WG.Peer)
    (hb : side < 2) (hbelow : NodesBelow d) (hparent : n.id ∉ sibling.nodeIds)
    (hr : RepAt d.nodes (rootWidth v4) base (Tree.fork n side .empty sibling)) :
    RepAt (gapInstalledAt d v4 base n side sibling addr cidr pid p).nodes (rootWidth v4) base
      (Tree.fork n side (requestedLeaf d.nextNode addr cidr pid) sibling) := by
  obtain ⟨hn, hs⟩ := gap_rep_parts hb hr
  have hne : d.nextNode ≠ n.id := Nat.ne_of_gt (hbelow n.id _ hn)
  have hs' : RepAt (gapInstalledAt d v4 base n side sibling addr cidr pid p).nodes
      (rootWidth v4) (.child n.id (1 - side)) sibling := by
    apply hs.congr
    intro id hi
    exact gapInstalledAt_nodes_other d v4 base n side sibling addr cidr pid p id
      (Nat.ne_of_gt (hs.ids_below hbelow id hi)) (fun he => hparent (he ▸ hi))
  have hcases : side = 0 ∨ side = 1 := by omega
  rcases hcases with rfl | rfl
  · refine ⟨?_, ?_, hs'⟩
    · simp [gapInstalledAt, connectedChild, allocated, gapParent, encode,
        Tree.root, requestedLeaf, requestedNode]
    · simp [RepAt, requestedLeaf, requestedNode, gapInstalledAt, connectedChild,
        allocated, Std.TreeMap.getElem_insert, Ne.symm hne, WG.newNode, encode, Tree.root]
  · refine ⟨?_, hs', ?_⟩
    · simp [gapInstalledAt, connectedChild, allocated, gapParent, encode,
        Tree.root, requestedLeaf, requestedNode]
    · simp [RepAt, requestedLeaf, requestedNode, gapInstalledAt, connectedChild,
        allocated, Std.TreeMap.getElem_insert, Ne.symm hne, WG.newNode, encode, Tree.root]

theorem gapInstalledAt_below (d : WG.Device) (v4 : Bool) (base : WG.Slot) (n : NodeData)
    (side : Nat) (sibling : Tree) (addr cidr pid : Nat) (p : WG.Peer)
    (hbelow : NodesBelow d) (hn : n.id < d.nextNode) :
    NodesBelow (gapInstalledAt d v4 base n side sibling addr cidr pid p) := by
  intro id node hget
  change id < d.nextNode + 1
  by_cases hf : d.nextNode = id
  · subst id
    exact Nat.lt_succ_self _
  by_cases hp : n.id = id
  · subst id
    exact Nat.lt_trans hn (Nat.lt_succ_self _)
  rw [gapInstalledAt_nodes_other d v4 base n side sibling addr cidr pid p id hf hp] at hget
  exact Nat.lt_trans (hbelow id node hget) (Nat.lt_succ_self _)

@[simp] theorem gapInstalledAt_roots (d : WG.Device) (v4 family : Bool) (base : WG.Slot) (n : NodeData)
    (side : Nat) (sibling : Tree) (addr cidr pid : Nat) (p : WG.Peer) :
    rootValue (gapInstalledAt d v4 base n side sibling addr cidr pid p) family = rootValue d family := by
  cases family <;> rfl

@[simp] theorem gapInstalledAt_seq (d : WG.Device) (v4 : Bool) (base : WG.Slot) (n : NodeData)
    (side : Nat) (sibling : Tree) (addr cidr pid : Nat) (p : WG.Peer) :
    (gapInstalledAt d v4 base n side sibling addr cidr pid p).peerAllowedips.seq = d.peerAllowedips.seq := rfl

theorem gapInstalledAt_other_rep (d : WG.Device) (v4 : Bool) (base : WG.Slot) (n : NodeData)
    (side : Nat) (sibling : Tree) (addr cidr pid : Nat) (p : WG.Peer)
    (hb : side < 2) (hbelow : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth v4) base (Tree.fork n side .empty sibling))
    (other : Tree) (ho : RepAt d.nodes (rootWidth (!v4)) (rootSlot (!v4)) other) :
    RepAt (gapInstalledAt d v4 base n side sibling addr cidr pid p).nodes
      (rootWidth (!v4)) (rootSlot (!v4)) other := by
  have hparent : n.id ∉ other.nodeIds := by
    intro hi
    obtain ⟨node, hn, hw⟩ := ho.resident_bitlen hi
    have he : node = gapParent (rootWidth v4) base n side sibling :=
      Option.some.inj (hn.symm.trans (gap_rep_parts hb hr).1)
    rw [he, gapParent_bitlen] at hw
    cases v4 <;> simp [rootWidth] at hw
  apply ho.congr
  intro id hi
  exact gapInstalledAt_nodes_other d v4 base n side sibling addr cidr pid p id
    (Nat.ne_of_gt (ho.ids_below hbelow id hi)) (fun he => hparent (he ▸ hi))

theorem context_gap_insertFresh (c : Context) (n : NodeData) (side : Nat) (sibling : Tree)
    (width fresh addr cidr pid : Nat) (hf : c.Follows width addr cidr)
    (hb : side < 2) (hlt : n.cidr < cidr)
    (hm : prefixBits width n.cidr n.addr = prefixBits width n.cidr addr)
    (hbit : bit width n.cidr addr = side) :
    (c.plug (Tree.fork n side .empty sibling)).insertFresh width fresh addr cidr pid =
      ⟨c.plug (Tree.fork n side (requestedLeaf fresh addr cidr pid) sibling),
        requestedEntry fresh addr cidr pid, 1⟩ := by
  rw [c.insertFresh _ fresh pid hf, gap_insertFresh n side sibling width fresh addr cidr pid hb hlt hm hbit]

theorem gapInstalledAt_context_rep (d : WG.Device) (v4 : Bool) (c : Context) (n : NodeData)
    (side : Nat) (sibling : Tree) (addr cidr pid : Nat) (p : WG.Peer)
    (hb : side < 2) (hbelow : NodesBelow d)
    (hnodup : (c.plug (Tree.fork n side .empty sibling)).nodeIds.Nodup)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (c.plug (Tree.fork n side .empty sibling))) :
    RepAt (gapInstalledAt d v4 (c.slot (rootSlot v4)) n side sibling addr cidr pid p).nodes
      (rootWidth v4) (rootSlot v4)
      (c.plug (Tree.fork n side (requestedLeaf d.nextNode addr cidr pid) sibling)) := by
  have hfocus := c.focus_rep _ _ hr
  have hnlocal := (Tree.fork_nodeIds_perm n side .empty sibling).nodup (c.focus_nodup _ hnodup)
  simp only [Tree.nodeIds, List.nil_append, List.nodup_cons] at hnlocal
  have hparent : n.id ∉ sibling.nodeIds := hnlocal.1
  apply c.rep_replace_sameRoot _ _ _ hr
    (gapInstalledAt_rep d v4 (c.slot (rootSlot v4)) n side sibling addr cidr pid p hb hbelow hparent hfocus)
    (by simp only [Tree.fork_root])
  intro id hi
  have hold : id ∈ (c.plug (Tree.fork n side .empty sibling)).nodeIds :=
    (c.mem_plug_nodeIds _ id).mpr (.inl hi)
  have hparentOutside : n.id ∉ (c.plug .empty).nodeIds :=
    c.focus_disjoint _ hnodup n.id (by simp [Tree.mem_fork_nodeIds])
  exact gapInstalledAt_nodes_other d v4 (c.slot (rootSlot v4)) n side sibling addr cidr pid p id
    (Nat.ne_of_gt (hr.ids_below hbelow id hold)) (fun he => hparentOutside (he ▸ hi))

end Leanux.Proofs.WG.AllowedIps
