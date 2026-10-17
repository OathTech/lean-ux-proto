import Leanux.Proofs.WG.AllowedIps.ChildMutation

/-! Representation after the original immediate-child insertion. Whole-store
freshness protects the new identifier; the parent is excluded from its sibling. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux

theorem gap_insertFresh (n : NodeData) (side : Nat) (sibling : Tree)
    (width fresh addr cidr pid : Nat) (hb : side < 2) (hlt : n.cidr < cidr)
    (hm : prefixBits width n.cidr n.addr = prefixBits width n.cidr addr)
    (hbit : bit width n.cidr addr = side) :
    (Tree.fork n side .empty sibling).insertFresh width fresh addr cidr pid =
      ⟨Tree.fork n side (requestedLeaf fresh addr cidr pid) sibling,
        requestedEntry fresh addr cidr pid, 1⟩ := by
  have h := (gapContext n side sibling).insertFresh .empty fresh pid
    (gapContext_follows n side sibling hb hlt hm hbit)
  simpa [gapContext_plug, Tree.insertFresh, graft] using h

theorem gapInstalled_nodes_other (d : WG.Device) (v4 : Bool) (n : NodeData)
    (side : Nat) (sibling : Tree) (addr cidr pid : Nat) (p : WG.Peer)
    (id : Nat) (hf : d.nextNode ≠ id) (hp : n.id ≠ id) :
    (gapInstalled d v4 n side sibling addr cidr pid p).nodes[id]? = d.nodes[id]? := by
  simp [gapInstalled, connectedChild, allocated, Std.TreeMap.getElem?_insert, hf, hp]

theorem gap_rep_parts {nodes : Std.TreeMap Nat WG.AipNode} {width : Nat}
    {base : WG.Slot} {n : NodeData} {side : Nat} {sibling : Tree} (hb : side < 2)
    (hr : RepAt nodes width base (Tree.fork n side .empty sibling)) :
    nodes[n.id]? = some (gapParent width base n side sibling) ∧
      RepAt nodes width (.child n.id (1 - side)) sibling := by
  have hs : side = 0 ∨ side = 1 := by omega
  rcases hs with rfl | rfl
  · exact ⟨hr.1, hr.2.2⟩
  · exact ⟨hr.1, hr.2.1⟩

theorem gapInstalled_rep (d : WG.Device) (v4 : Bool) (n : NodeData)
    (side : Nat) (sibling : Tree) (addr cidr pid : Nat) (p : WG.Peer)
    (hb : side < 2) (hbelow : NodesBelow d) (hparent : n.id ∉ sibling.nodeIds)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (Tree.fork n side .empty sibling)) :
    RepAt (gapInstalled d v4 n side sibling addr cidr pid p).nodes (rootWidth v4) (rootSlot v4)
      (Tree.fork n side (requestedLeaf d.nextNode addr cidr pid) sibling) := by
  obtain ⟨hn, hs⟩ := gap_rep_parts hb hr
  have hne : d.nextNode ≠ n.id := Nat.ne_of_gt (hbelow n.id _ hn)
  have hs' : RepAt (gapInstalled d v4 n side sibling addr cidr pid p).nodes
      (rootWidth v4) (.child n.id (1 - side)) sibling := by
    apply hs.congr
    intro id hi
    exact gapInstalled_nodes_other d v4 n side sibling addr cidr pid p id
      (Nat.ne_of_gt (hs.ids_below hbelow id hi)) (fun he => hparent (he ▸ hi))
  have hcases : side = 0 ∨ side = 1 := by omega
  rcases hcases with rfl | rfl
  · refine ⟨?_, ?_, hs'⟩
    · simp [gapInstalled, connectedChild, allocated, gapParent, encode,
        Tree.root, requestedLeaf, requestedNode]
    · simp [RepAt, requestedLeaf, requestedNode, gapInstalled, connectedChild,
        allocated, Std.TreeMap.getElem_insert, Ne.symm hne, WG.newNode, encode, Tree.root]
  · refine ⟨?_, hs', ?_⟩
    · simp [gapInstalled, connectedChild, allocated, gapParent, encode,
        Tree.root, requestedLeaf, requestedNode]
    · simp [RepAt, requestedLeaf, requestedNode, gapInstalled, connectedChild,
        allocated, Std.TreeMap.getElem_insert, Ne.symm hne, WG.newNode, encode, Tree.root]

theorem gapInstalled_below (d : WG.Device) (v4 : Bool) (n : NodeData)
    (side : Nat) (sibling : Tree) (addr cidr pid : Nat) (p : WG.Peer)
    (hbelow : NodesBelow d) (hn : n.id < d.nextNode) :
    NodesBelow (gapInstalled d v4 n side sibling addr cidr pid p) := by
  intro id node hget
  change id < d.nextNode + 1
  by_cases hf : d.nextNode = id
  · subst id
    exact Nat.lt_succ_self _
  by_cases hp : n.id = id
  · subst id
    exact Nat.lt_trans hn (Nat.lt_succ_self _)
  rw [gapInstalled_nodes_other d v4 n side sibling addr cidr pid p id hf hp] at hget
  exact Nat.lt_trans (hbelow id node hget) (Nat.lt_succ_self _)

@[simp] theorem gapInstalled_roots (d : WG.Device) (v4 family : Bool) (n : NodeData)
    (side : Nat) (sibling : Tree) (addr cidr pid : Nat) (p : WG.Peer) :
    rootValue (gapInstalled d v4 n side sibling addr cidr pid p) family = rootValue d family := by
  cases family <;> rfl

@[simp] theorem gapInstalled_seq (d : WG.Device) (v4 : Bool) (n : NodeData)
    (side : Nat) (sibling : Tree) (addr cidr pid : Nat) (p : WG.Peer) :
    (gapInstalled d v4 n side sibling addr cidr pid p).peerAllowedips.seq = d.peerAllowedips.seq := rfl

theorem gapInstalled_other_rep (d : WG.Device) (v4 : Bool) (n : NodeData)
    (side : Nat) (sibling : Tree) (addr cidr pid : Nat) (p : WG.Peer)
    (hb : side < 2) (hbelow : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (Tree.fork n side .empty sibling))
    (other : Tree) (ho : RepAt d.nodes (rootWidth (!v4)) (rootSlot (!v4)) other) :
    RepAt (gapInstalled d v4 n side sibling addr cidr pid p).nodes
      (rootWidth (!v4)) (rootSlot (!v4)) other := by
  have hparent : n.id ∉ other.nodeIds := by
    intro hi
    obtain ⟨node, hn, hw⟩ := ho.resident_bitlen hi
    have he : node = gapParent (rootWidth v4) (rootSlot v4) n side sibling :=
      Option.some.inj (hn.symm.trans (gap_rep_parts hb hr).1)
    rw [he, gapParent_bitlen] at hw
    cases v4 <;> simp [rootWidth] at hw
  apply ho.congr
  intro id hi
  exact gapInstalled_nodes_other d v4 n side sibling addr cidr pid p id
    (Nat.ne_of_gt (ho.ids_below hbelow id hi)) (fun he => hparent (he ▸ hi))

end Leanux.Proofs.WG.AllowedIps
