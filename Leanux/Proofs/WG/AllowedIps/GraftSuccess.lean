import Leanux.Proofs.WG.AllowedIps.GraftStore

/-! Structural refinement of the successful selected-root graft endpoints.
The executable insertion algorithm remains `Tree.insertFresh`. -/
set_option maxHeartbeats 1000000
namespace Leanux.Proofs.WG.AllowedIps
open Leanux

theorem graftOne_rep (d : WG.Device) (v4 : Bool) (n : NodeData) (l r : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) (hb : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (.node n l r))
    (hn : (Tree.node n l r).nodeIds.Nodup) :
    RepAt (graftOne d v4 n.id (encode (rootWidth v4) (rootSlot v4) n l r)
      addr cidr pid p).nodes (rootWidth v4) (rootSlot v4)
      (Tree.fork (requestedNode d.nextNode addr cidr pid)
        (bit (rootWidth v4) cidr n.addr) (.node n l r) .empty) := by
  have hid := hb n.id _ hr.1
  have hne : d.nextNode ≠ n.id := Nat.ne_of_gt hid
  have hdesc : n.id ∉ l.nodeIds ++ r.nodeIds := (List.nodup_cons.mp hn).1
  let out := graftOne d v4 n.id (encode (rootWidth v4) (rootSlot v4) n l r) addr cidr pid p
  have hf : ∀ id ∈ l.nodeIds ++ r.nodeIds, out.nodes[id]? = d.nodes[id]? := by
    intro id hi
    have hi' : id ∈ (Tree.node n l r).nodeIds := List.mem_cons_of_mem _ hi
    exact graftOne_nodes_other d v4 n.id _ addr cidr pid p id
      (Nat.ne_of_gt (hr.ids_below hb id hi')) (fun he => hdesc (he ▸ hi))
  have hold : RepAt out.nodes (rootWidth v4)
      (.child d.nextNode (bit (rootWidth v4) cidr n.addr)) (.node n l r) := by
    apply hr.root_reparent ?_ hf
    simp [out, graftOne, connectedRoot, rootWrite, connectedChild, graftListed,
      allocated, Std.TreeMap.getElem_insert, hne, encode]
  have hbit := bit_lt_two (rootWidth v4) cidr n.addr
  have hcases : bit (rootWidth v4) cidr n.addr = 0 ∨ bit (rootWidth v4) cidr n.addr = 1 := by omega
  rcases hcases with hs | hs
  · simp only [Tree.fork, hs, ↓reduceIte]
    refine ⟨?_, ?_, trivial⟩
    · simp [graftOne, connectedRoot, rootWrite, connectedChild, graftListed, allocated,
        encode, requestedNode, WG.newNode, Tree.root, hs]
    · simpa only [out, hs, requestedNode] using hold
  · simp only [Tree.fork, hs, show ¬ (1 : Nat) = 0 from by omega, ↓reduceIte]
    refine ⟨?_, trivial, ?_⟩
    · simp [graftOne, connectedRoot, rootWrite, connectedChild, graftListed, allocated,
        encode, requestedNode, WG.newNode, Tree.root, hs]
    · simpa only [out, hs, requestedNode] using hold

theorem graftTwo_rep (d : WG.Device) (v4 : Bool) (n : NodeData) (l r : Tree)
    (addr cidr pid split : Nat) (p : WG.Peer) (hb : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (.node n l r))
    (hn : (Tree.node n l r).nodeIds.Nodup)
    (hbits : bit (rootWidth v4) split n.addr ≠ bit (rootWidth v4) split addr) :
    RepAt (graftTwo d v4 n.id (encode (rootWidth v4) (rootSlot v4) n l r)
      addr cidr pid split p).nodes (rootWidth v4) (rootSlot v4)
      (Tree.fork ⟨d.nextNode + 1, addr, split, none⟩
        (bit (rootWidth v4) split n.addr) (.node n l r) (requestedLeaf d.nextNode addr cidr pid)) := by
  have hid := hb n.id _ hr.1
  have hne : d.nextNode ≠ n.id := Nat.ne_of_gt hid
  have hme : d.nextNode + 1 ≠ n.id := Nat.ne_of_gt (Nat.lt_succ_of_lt hid)
  have hdesc : n.id ∉ l.nodeIds ++ r.nodeIds := (List.nodup_cons.mp hn).1
  let out := graftTwo d v4 n.id (encode (rootWidth v4) (rootSlot v4) n l r) addr cidr pid split p
  have hf : ∀ id ∈ l.nodeIds ++ r.nodeIds, out.nodes[id]? = d.nodes[id]? := by
    intro id hi
    have hi' : id ∈ (Tree.node n l r).nodeIds := List.mem_cons_of_mem _ hi
    have hlt := hr.ids_below hb id hi'
    exact graftTwo_nodes_other d v4 n.id _ addr cidr pid split p id
      (Nat.ne_of_gt hlt) (Nat.ne_of_gt (Nat.lt_succ_of_lt hlt)) (fun he => hdesc (he ▸ hi))
  have hold : RepAt out.nodes (rootWidth v4)
      (.child (d.nextNode + 1) (bit (rootWidth v4) split n.addr)) (.node n l r) := by
    apply hr.root_reparent ?_ hf
    simp [out, graftTwo, connectedRoot, rootWrite, connectedChild, graftListed,
      allocated, Std.TreeMap.getElem_insert, hne, hme, encode]
  have hleaf : RepAt out.nodes (rootWidth v4)
      (.child (d.nextNode + 1) (bit (rootWidth v4) split addr))
      (requestedLeaf d.nextNode addr cidr pid) := by
    refine ⟨?_, trivial, trivial⟩
    simp [out, graftTwo, connectedRoot, rootWrite, connectedChild, graftListed,
      allocated, Std.TreeMap.getElem_insert, requestedNode, encode, WG.newNode, Tree.root]
  have h0 := bit_lt_two (rootWidth v4) split n.addr
  have h1 := bit_lt_two (rootWidth v4) split addr
  have hcases : (bit (rootWidth v4) split n.addr = 0 ∧ bit (rootWidth v4) split addr = 1) ∨
      (bit (rootWidth v4) split n.addr = 1 ∧ bit (rootWidth v4) split addr = 0) := by omega
  rcases hcases with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · simp only [Tree.fork, hs, ↓reduceIte]
    refine ⟨?_, ?_, ?_⟩
    · simp [graftTwo, connectedRoot, rootWrite, connectedChild, graftListed, allocated,
        encode, requestedNode, requestedLeaf, WG.newNode, Tree.root, hs, ht]
    · simpa only [out, hs, requestedNode] using hold
    · simpa only [out, ht] using hleaf
  · simp only [Tree.fork, hs, show ¬ (1 : Nat) = 0 from by omega, ↓reduceIte]
    refine ⟨?_, ?_, ?_⟩
    · simp [graftTwo, connectedRoot, rootWrite, connectedChild, graftListed, allocated,
        encode, requestedNode, requestedLeaf, WG.newNode, Tree.root, hs, ht]
    · simpa only [out, ht] using hleaf
    · simpa only [out, hs, requestedNode] using hold

theorem root_graft_insertFresh (width fresh addr cidr pid : Nat) (n : NodeData) (l r : Tree)
    (hstop : ¬ (n.cidr ≤ cidr ∧ prefixBits width n.cidr n.addr = prefixBits width n.cidr addr)) :
    (Tree.node n l r).insertFresh width fresh addr cidr pid = graft width fresh addr cidr pid (.node n l r) := by
  rw [Tree.insertFresh, if_neg hstop]

theorem graftInstalled_rep (d : WG.Device) (v4 : Bool) (n : NodeData) (l r : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) (hb : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (.node n l r))
    (hn : (Tree.node n l r).nodeIds.Nodup)
    (hv : (Tree.node n l r).Valid (rootWidth v4)) (ha : addr < 2 ^ rootWidth v4)
    (hstop : ¬ (n.cidr ≤ cidr ∧ prefixBits (rootWidth v4) n.cidr n.addr =
      prefixBits (rootWidth v4) n.cidr addr)) :
    RepAt (graftInstalled d v4 n.id (encode (rootWidth v4) (rootSlot v4) n l r)
      addr cidr pid p).nodes (rootWidth v4) (rootSlot v4)
      ((Tree.node n l r).insertFresh (rootWidth v4) d.nextNode addr cidr pid).tree := by
  rw [root_graft_insertFresh _ _ _ _ _ _ _ _ hstop]
  by_cases hs : min cidr (common (rootWidth v4) n.addr addr) = cidr
  · simpa [graftInstalled, encode, graft, hs] using
      graftOne_rep d v4 n l r addr cidr pid p hb hr hn
  · have hg := graftable_of_stopped hv ha hstop
    obtain ⟨he, _, _, hbits⟩ := graft_split_properties hv ha hg hs
    have hbits' : bit (rootWidth v4) (min cidr (common (rootWidth v4) n.addr addr)) n.addr ≠
        bit (rootWidth v4) (min cidr (common (rootWidth v4) n.addr addr)) addr := by
      simpa only [he] using hbits
    simpa [graftInstalled, encode, graft, hs] using
      graftTwo_rep d v4 n l r addr cidr pid _ p hb hr hn hbits'

theorem graftInstalled_nodes_other (d : WG.Device) (v4 : Bool) (id : Nat) (old : WG.AipNode)
    (addr cidr pid : Nat) (p : WG.Peer) (q : Nat)
    (hf : d.nextNode ≠ q) (hm : d.nextNode + 1 ≠ q) (ho : id ≠ q) :
    (graftInstalled d v4 id old addr cidr pid p).nodes[q]? = d.nodes[q]? := by
  unfold graftInstalled
  dsimp only
  split
  · exact graftOne_nodes_other d v4 id old addr cidr pid p q hf ho
  · exact graftTwo_nodes_other d v4 id old addr cidr pid _ p q hf hm ho

theorem graftInstalled_below (d : WG.Device) (v4 : Bool) (id : Nat) (old : WG.AipNode)
    (addr cidr pid : Nat) (p : WG.Peer) (hb : NodesBelow d) (hid : id < d.nextNode) :
    NodesBelow (graftInstalled d v4 id old addr cidr pid p) := by
  unfold graftInstalled
  dsimp only
  split
  · intro q node hget
    change q < d.nextNode + 1
    by_cases hf : d.nextNode = q
    · rw [← hf]; exact Nat.lt_succ_self _
    by_cases ho : id = q
    · rw [← ho]; exact Nat.lt_succ_of_lt hid
    rw [graftOne_nodes_other d v4 id old addr cidr pid p q hf ho] at hget
    exact Nat.lt_succ_of_lt (hb q node hget)
  · intro q node hget
    change q < (d.nextNode + 1) + 1
    by_cases hf : d.nextNode = q
    · rw [← hf]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)
    by_cases hm : d.nextNode + 1 = q
    · rw [← hm]; exact Nat.lt_succ_self _
    by_cases ho : id = q
    · rw [← ho]; exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hid)
    rw [graftTwo_nodes_other d v4 id old addr cidr pid _ p q hf hm ho] at hget
    exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt (hb q node hget))

theorem graftInstalled_other_rep (d : WG.Device) (v4 : Bool) (n : NodeData) (l r : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) (hb : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (.node n l r))
    (other : Tree) (ho : RepAt d.nodes (rootWidth (!v4)) (rootSlot (!v4)) other) :
    RepAt (graftInstalled d v4 n.id (encode (rootWidth v4) (rootSlot v4) n l r)
      addr cidr pid p).nodes (rootWidth (!v4)) (rootSlot (!v4)) other := by
  have hroot : n.id ∉ other.nodeIds := by
    intro hi
    obtain ⟨node, hget, hwidth⟩ := ho.resident_bitlen hi
    have he : node = encode (rootWidth v4) (rootSlot v4) n l r :=
      Option.some.inj (hget.symm.trans hr.1)
    rw [he] at hwidth
    cases v4 <;> simp [encode, rootWidth] at hwidth
  apply ho.congr
  intro id hi
  have hlt := ho.ids_below hb id hi
  exact graftInstalled_nodes_other d v4 n.id _ addr cidr pid p id
    (Nat.ne_of_gt hlt) (Nat.ne_of_gt (Nat.lt_succ_of_lt hlt)) (fun he => hroot (he ▸ hi))

theorem graftInstalled_insert_metadata (d : WG.Device) (v4 : Bool) (n : NodeData) (l r : Tree)
    (addr cidr pid : Nat) (p : WG.Peer)
    (hstop : ¬ (n.cidr ≤ cidr ∧ prefixBits (rootWidth v4) n.cidr n.addr =
      prefixBits (rootWidth v4) n.cidr addr)) :
    let inserted := (Tree.node n l r).insertFresh (rootWidth v4) d.nextNode addr cidr pid
    let installed := graftInstalled d v4 n.id (encode (rootWidth v4) (rootSlot v4) n l r) addr cidr pid p
    installed.nextNode = d.nextNode + inserted.allocations ∧
      rootValue installed v4 = inserted.tree.root ∧
      rootValue installed (!v4) = rootValue d (!v4) ∧
      installed.peerAllowedips.seq = d.peerAllowedips.seq := by
  dsimp only
  rw [root_graft_insertFresh _ _ _ _ _ _ _ _ hstop]
  have hm := graftInstalled_metadata d v4 n.id (encode (rootWidth v4) (rootSlot v4) n l r) addr cidr pid p
  by_cases hs : min cidr (common (rootWidth v4) n.addr addr) = cidr
  · simpa [graft, encode, hs, requestedNode] using hm
  · simpa [graft, encode, hs] using hm

end Leanux.Proofs.WG.AllowedIps
