import Leanux.Proofs.WG.AllowedIps.DeepChildStore
import Leanux.Proofs.WG.AllowedIps.ExactStore
import Leanux.Proofs.WG.AllowedIps.DeepGraft

/-! Reusable original insertion-case contracts. These are the established
empty-root, empty-child, exact-prefix and nonempty-graft contracts; the public
result declarations retain their signatures and export these proofs. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux

theorem case_add_empty_root_correct (w w' : World) (d : WG.Device)
    (hd : w.k.wg = some d) (v4 : Bool) (addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (he : rootValue d v4 = none)
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
    (hb : NodesBelow d) (other : Tree)
    (ho : RepAt d.nodes (rootWidth (!v4)) (rootSlot (!v4)) other) (result : Int)
    (hr : (WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w = .ok (result, w')) :
    let installed := emptyInstalled d v4 addr cidr pid p
    let tree := (Tree.empty.insertFresh (rootWidth v4) d.nextNode addr cidr pid).tree
    (result = -ENOMEM ∧ w'.k = w.k) ∨
      (result = 0 ∧ w'.k = { w.k with wg := some installed } ∧
        NodesBelow installed ∧ rootValue installed v4 = tree.root ∧
        RepAt installed.nodes (rootWidth v4) (rootSlot v4) tree ∧ tree.Valid (rootWidth v4) ∧
        rootValue installed (!v4) = rootValue d (!v4) ∧
        RepAt installed.nodes (rootWidth (!v4)) (rootSlot (!v4)) other) := by
  rcases add_empty_exact w w' d hd v4 addr cidr pid p hp he hc result hr with hf | hs
  · exact .inl hf
  · refine .inr ⟨hs.1, hs.2, emptyInstalled_below d hb v4 addr cidr pid p, ?_,
      emptyInstalled_rep d v4 addr cidr pid p,
      Tree.insertFresh_valid (by trivial) ha hc d.nextNode pid,
      emptyInstalled_other_root d v4 addr cidr pid p,
      emptyInstalled_other_rep d hb v4 addr cidr pid p other ho⟩
    exact emptyInstalled_root d v4 addr cidr pid p

theorem case_add_context_empty_child_correct (w w' : World) (d : WG.Device)
    (hd : w.k.wg = some d) (v4 : Bool) (c : Context) (n : NodeData) (side : Nat) (sibling : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (hroot : rootValue d v4 = (c.plug (Tree.fork n side .empty sibling)).root)
    (hb : side < 2) (hbelow : NodesBelow d)
    (hnodup : (c.plug (Tree.fork n side .empty sibling)).nodeIds.Nodup)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (c.plug (Tree.fork n side .empty sibling)))
    (hv : (c.plug (Tree.fork n side .empty sibling)).Valid (rootWidth v4))
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
    (hf : c.Follows (rootWidth v4) addr cidr) (hlt : n.cidr < cidr)
    (hm : prefixBits (rootWidth v4) n.cidr n.addr = prefixBits (rootWidth v4) n.cidr addr)
    (hbit : bit (rootWidth v4) n.cidr addr = side)
    (other : Tree) (ho : RepAt d.nodes (rootWidth (!v4)) (rootSlot (!v4)) other) (result : Int)
    (hreturn : (WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w = .ok (result, w')) :
    let installed := gapInstalledAt d v4 (c.slot (rootSlot v4)) n side sibling addr cidr pid p
    let inserted := (c.plug (Tree.fork n side .empty sibling)).insertFresh
      (rootWidth v4) d.nextNode addr cidr pid
    (result = -ENOMEM ∧ w'.k = w.k) ∨
      (result = 0 ∧ w'.k = { w.k with wg := some installed } ∧ NodesBelow installed ∧
        rootValue installed v4 = inserted.tree.root ∧
        RepAt installed.nodes (rootWidth v4) (rootSlot v4) inserted.tree ∧
        inserted.tree.Valid (rootWidth v4) ∧ inserted.tree.nodeIds.Nodup ∧
        installed.nextNode = d.nextNode + 1 ∧ installed.peerAllowedips.seq = d.peerAllowedips.seq ∧
        (∀ family, rootValue installed family = rootValue d family) ∧
        RepAt installed.nodes (rootWidth (!v4)) (rootSlot (!v4)) other) := by
  have outcome := (Leanux.Proofs.Framing.hoare_iff_triple _ _ _).mpr
    (add_context_gap_wp w.k d hd v4 c n side sibling addr cidr pid p hp hroot hb hbelow hr hv
      ha hc hf hlt hm hbit) w result w' rfl hreturn
  rcases outcome with hfail | hs
  · exact .inl hfail
  have shape := context_gap_insertFresh c n side sibling (rootWidth v4) d.nextNode addr cidr pid
    hf hb hlt hm hbit
  have hfocus := c.focus_rep _ _ hr
  have hn := (gap_rep_parts hb hfocus).1
  refine .inr ⟨hs.1, hs.2,
    gapInstalledAt_below d v4 (c.slot (rootSlot v4)) n side sibling addr cidr pid p hbelow
      (hbelow n.id _ hn), ?_, ?_, Tree.insertFresh_valid hv ha hc d.nextNode pid,
    Tree.insertFresh_nodeIds_nodup hnodup (hr.ids_below hbelow) (rootWidth v4) addr cidr pid,
    rfl, rfl, (fun family => gapInstalledAt_roots d v4 family (c.slot (rootSlot v4)) n side sibling addr cidr pid p),
    gapInstalledAt_other_rep d v4 (c.slot (rootSlot v4)) n side sibling addr cidr pid p hb hbelow hfocus other ho⟩
  · simp only [shape]
    exact (gapInstalledAt_roots d v4 v4 (c.slot (rootSlot v4)) n side sibling addr cidr pid p).trans
      (hroot.trans (c.root_congr (by simp only [Tree.fork_root])).symm)
  · simpa only [shape] using
      gapInstalledAt_context_rep d v4 c n side sibling addr cidr pid p hb hbelow hnodup hr

theorem case_add_context_exact_correct (w : World) (d : WG.Device)
    (hd : w.k.wg = some d) (v4 : Bool) (c : Context) (n : NodeData) (l r : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (hroot : rootValue d v4 = (c.plug (.node n l r)).root)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (c.plug (.node n l r)))
    (hv : (c.plug (.node n l r)).Valid (rootWidth v4))
    (hnodup : (c.plug (.node n l r)).nodeIds.Nodup)
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
    (hf : c.Follows (rootWidth v4) addr cidr) (hn : n.cidr = cidr)
    (hm : prefixBits (rootWidth v4) n.cidr n.addr = prefixBits (rootWidth v4) n.cidr addr)
    (other : Tree) (ho : RepAt d.nodes (rootWidth (!v4)) (rootSlot (!v4)) other) :
    let installed := exactInstalled d n.id (encode (rootWidth v4) (c.slot (rootSlot v4)) n l r) pid p
    let inserted := (c.plug (.node n l r)).insertFresh (rootWidth v4) d.nextNode addr cidr pid
    ∃ w', (WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w = .ok (0, w') ∧
      w'.k = { w.k with wg := some installed } ∧
      rootValue installed v4 = inserted.tree.root ∧
      RepAt installed.nodes (rootWidth v4) (rootSlot v4) inserted.tree ∧
      inserted.tree.Valid (rootWidth v4) ∧ inserted.tree.nodeIds = (c.plug (.node n l r)).nodeIds ∧
      inserted.tree.nodeIds.Nodup ∧ inserted.allocations = 0 ∧
      installed.nextNode = d.nextNode ∧ installed.peerAllowedips.seq = d.peerAllowedips.seq ∧
      (∀ f, rootValue installed f = rootValue d f) ∧
      RepAt installed.nodes (rootWidth (!v4)) (rootSlot (!v4)) other ∧
      installed.peers[pid]? = some { p with allowedipsList := WG.listRemove p.allowedipsList n.id ++ [n.id] } ∧
      (∀ q : Nat, pid ≠ q → installed.peers[q]? = (d.peers[q]?).map (unlist n.id)) ∧
      (∀ q : Nat, (installed.peers[q]?).map WG.Peer.internalId = (d.peers[q]?).map WG.Peer.internalId) ∧
      (NodesBelow d → NodesBelow installed) := by
  obtain ⟨result, w', hrun, hret, hk⟩ := (Leanux.Proofs.Framing.total_iff_run _ _ _).mp
    (add_context_exact_wp w.k d hd v4 c n l r addr cidr pid p hp hroot hr hv ha hc hf hn hm) w rfl
  subst result
  have shape := context_exact_insertFresh c n l r (rootWidth v4) d.nextNode addr cidr pid hf hn hm
  have hids : ((c.plug (.node n l r)).insertFresh (rootWidth v4) d.nextNode addr cidr pid).tree.nodeIds =
      (c.plug (.node n l r)).nodeIds := by
    rw [shape]
    exact c.nodeIds_congr rfl
  refine ⟨w', hrun, hk, ?_, ?_, Tree.insertFresh_valid hv ha hc d.nextNode pid,
    hids, hids ▸ hnodup, ?_, rfl, rfl, ?_, ?_, exactInstalled_peer ..,
    exactInstalled_other_peer d n.id _ pid p,
    exactInstalled_identity d n.id _ pid p hp, ?_⟩
  · rw [shape]
    exact hroot.trans (c.root_congr (before := .node n l r)
      (after := .node { n with peer := some pid } l r) rfl).symm
  · rw [shape]
    exact exactInstalled_context_rep d (rootWidth v4) (rootSlot v4) c n l r pid p hr hnodup
  · rw [shape]
  · intro f
    cases f <;> rfl
  · exact exactInstalled_other_rep d v4 (c.slot (rootSlot v4)) n l r pid p
      (c.focus_rep _ _ hr) other ho
  · intro hb
    exact exactInstalled_below d n.id _ pid p hb (hb n.id _ (c.focus_rep _ _ hr).1)

theorem case_add_root_graft_endpoints (w w' : World) (d : WG.Device)
    (hd : w.k.wg = some d) (v4 : Bool) (n : NodeData) (l r : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (hroot : rootValue d v4 = some n.id) (hb : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (.node n l r))
    (hv : (Tree.node n l r).Valid (rootWidth v4))
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
    (hstop : ¬ (n.cidr ≤ cidr ∧ prefixBits (rootWidth v4) n.cidr n.addr =
      prefixBits (rootWidth v4) n.cidr addr)) (result : Int)
    (hreturn : (WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w = .ok (result, w')) :
    (result = -ENOMEM ∧ w'.k = w.k) ∨
      (result = -ENOMEM ∧ min cidr (common (rootWidth v4) n.addr addr) ≠ cidr ∧
        w'.k = { w.k with wg := some (graftRolledBack d (rootWidth v4) addr cidr pid p) }) ∨
      (result = 0 ∧ w'.k = { w.k with wg := some (graftInstalled d v4 n.id
        (encode (rootWidth v4) (rootSlot v4) n l r) addr cidr pid p) }) :=
  (Leanux.Proofs.Framing.hoare_iff_triple _ _ _).mpr
    (add_root_graft_wp w.k d hd v4 n l r addr cidr pid p hp hroot hb hr hv ha hc hstop)
    w result w' rfl hreturn

theorem case_add_root_graft_correct (w w' : World) (d : WG.Device)
    (hd : w.k.wg = some d) (v4 : Bool) (n : NodeData) (l r : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (hroot : rootValue d v4 = some n.id) (hb : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (.node n l r))
    (hn : (Tree.node n l r).nodeIds.Nodup)
    (hv : (Tree.node n l r).Valid (rootWidth v4))
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
    (hstop : ¬ (n.cidr ≤ cidr ∧ prefixBits (rootWidth v4) n.cidr n.addr =
      prefixBits (rootWidth v4) n.cidr addr))
    (other : Tree) (ho : RepAt d.nodes (rootWidth (!v4)) (rootSlot (!v4)) other)
    (hreturn : (WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w = .ok (0, w')) :
    let inserted := (Tree.node n l r).insertFresh (rootWidth v4) d.nextNode addr cidr pid
    let installed := graftInstalled d v4 n.id (encode (rootWidth v4) (rootSlot v4) n l r) addr cidr pid p
    w'.k = { w.k with wg := some installed } ∧ NodesBelow installed ∧
      rootValue installed v4 = inserted.tree.root ∧
      RepAt installed.nodes (rootWidth v4) (rootSlot v4) inserted.tree ∧
      inserted.tree.Valid (rootWidth v4) ∧ inserted.tree.nodeIds.Nodup ∧
      ((Tree.node n l r).Compressed → inserted.tree.Compressed) ∧
      installed.nextNode = d.nextNode + inserted.allocations ∧
      rootValue installed (!v4) = rootValue d (!v4) ∧
      installed.peerAllowedips.seq = d.peerAllowedips.seq ∧
      RepAt installed.nodes (rootWidth (!v4)) (rootSlot (!v4)) other := by
  have outcome := case_add_root_graft_endpoints w w' d hd v4 n l r addr cidr pid p
    hp hroot hb hr hv ha hc hstop 0 hreturn
  rcases outcome with hf | hf | hs
  · simp [ENOMEM] at hf
  · simp [ENOMEM] at hf
  have hm := graftInstalled_insert_metadata d v4 n l r addr cidr pid p hstop
  exact ⟨hs.2, graftInstalled_below d v4 n.id _ addr cidr pid p hb (hb n.id _ hr.1),
    hm.2.1, graftInstalled_rep d v4 n l r addr cidr pid p hb hr hn hv ha hstop,
    Tree.insertFresh_valid hv ha hc d.nextNode pid,
    Tree.insertFresh_nodeIds_nodup hn (hr.ids_below hb) (rootWidth v4) addr cidr pid,
    fun h => Tree.insertFresh_compressed h (rootWidth v4) d.nextNode addr cidr pid,
    hm.1, hm.2.2.1, hm.2.2.2, graftInstalled_other_rep d v4 n l r addr cidr pid p hb hr other ho⟩

theorem case_add_context_graft_endpoints (w w' : World) (d : WG.Device) (hd : w.k.wg = some d)
    (v4 : Bool) (c : Context) (parent : NodeData) (side : Nat) (sibling : Tree)
    (n : NodeData) (l r : Tree) (addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p)
    (hroot : rootValue d v4 = (c.plug (Tree.fork parent side (.node n l r) sibling)).root)
    (hb : side < 2) (hbelow : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (c.plug (Tree.fork parent side (.node n l r) sibling)))
    (hv : (c.plug (Tree.fork parent side (.node n l r) sibling)).Valid (rootWidth v4))
    (hn : (c.plug (Tree.fork parent side (.node n l r) sibling)).nodeIds.Nodup)
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
    (hf : c.Follows (rootWidth v4) addr cidr) (hlt : parent.cidr < cidr)
    (hm : prefixBits (rootWidth v4) parent.cidr parent.addr = prefixBits (rootWidth v4) parent.cidr addr)
    (hbit : bit (rootWidth v4) parent.cidr addr = side)
    (hstop : ¬ (n.cidr ≤ cidr ∧ prefixBits (rootWidth v4) n.cidr n.addr = prefixBits (rootWidth v4) n.cidr addr))
    (ret : Int) (hreturn : (WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w = .ok (ret, w')) :
    (ret = -ENOMEM ∧ w'.k = w.k) ∨
      (ret = -ENOMEM ∧ min cidr (common (rootWidth v4) n.addr addr) ≠ cidr ∧
        w'.k = { w.k with wg := some (graftRolledBack d (rootWidth v4) addr cidr pid p) }) ∨
      (ret = 0 ∧ w'.k = { w.k with wg := some (contextGraftInstalled d v4
        (c.slot (rootSlot v4)) parent side sibling n l r addr cidr pid p) }) := by
  have spec := add_context_graft_wp w.k d hd v4 c parent side sibling n l r addr cidr pid p
    hp hroot hb hbelow hr hv hn ha hc hf hlt hm hbit hstop
  exact (Leanux.Proofs.Framing.hoare_iff_triple _ _ _).mpr spec w ret w' rfl hreturn

theorem case_add_context_graft_correct (w w' : World) (d : WG.Device) (hd : w.k.wg = some d)
    (v4 : Bool) (c : Context) (parent : NodeData) (side : Nat) (sibling : Tree)
    (n : NodeData) (l r : Tree) (addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p)
    (hroot : rootValue d v4 = (c.plug (Tree.fork parent side (.node n l r) sibling)).root)
    (hb : side < 2) (hbelow : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (c.plug (Tree.fork parent side (.node n l r) sibling)))
    (hv : (c.plug (Tree.fork parent side (.node n l r) sibling)).Valid (rootWidth v4))
    (hn : (c.plug (Tree.fork parent side (.node n l r) sibling)).nodeIds.Nodup)
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
    (hf : c.Follows (rootWidth v4) addr cidr) (hlt : parent.cidr < cidr)
    (hm : prefixBits (rootWidth v4) parent.cidr parent.addr = prefixBits (rootWidth v4) parent.cidr addr)
    (hbit : bit (rootWidth v4) parent.cidr addr = side)
    (hstop : ¬ (n.cidr ≤ cidr ∧ prefixBits (rootWidth v4) n.cidr n.addr = prefixBits (rootWidth v4) n.cidr addr))
    (other : Tree) (ho : RepAt d.nodes (rootWidth (!v4)) (rootSlot (!v4)) other)
    (hreturn : (WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w = .ok (0, w')) :
    let old := c.plug (Tree.fork parent side (.node n l r) sibling)
    let inserted := old.insertFresh (rootWidth v4) d.nextNode addr cidr pid
    let installed := contextGraftInstalled d v4 (c.slot (rootSlot v4)) parent side sibling n l r addr cidr pid p
    w'.k = { w.k with wg := some installed } ∧ NodesBelow installed ∧
      rootValue installed v4 = inserted.tree.root ∧
      RepAt installed.nodes (rootWidth v4) (rootSlot v4) inserted.tree ∧
      inserted.tree.Valid (rootWidth v4) ∧ inserted.tree.nodeIds.Nodup ∧
      (old.Compressed → inserted.tree.Compressed) ∧
      installed.nextNode = d.nextNode + inserted.allocations ∧
      rootValue installed (!v4) = rootValue d (!v4) ∧
      installed.peerAllowedips.seq = d.peerAllowedips.seq ∧
      RepAt installed.nodes (rootWidth (!v4)) (rootSlot (!v4)) other := by
  have outcome := case_add_context_graft_endpoints w w' d hd v4 c parent side sibling n l r addr cidr pid p hp hroot hb hbelow hr hv hn ha hc hf hlt hm hbit hstop 0 hreturn
  rcases outcome with h | h | h
  · simp [ENOMEM] at h
  · simp [ENOMEM] at h
  have hlocal := c.focus_rep _ _ hr
  obtain ⟨hparent, hfocus, _⟩ := fork_rep_parts hb hlocal
  have hvfocus : (Tree.node n l r).Valid (rootWidth v4) := by
    have hg := (gapContext parent side sibling).focus_valid (width := rootWidth v4) (.node n l r)
    exact hg (by simpa only [gapContext_plug] using c.focus_valid _ hv)
  have hmeta := contextGraftInstalled_insert_metadata d v4 c parent side sibling n l r addr cidr pid p
    hroot hf hb hlt hm hbit hstop
  have represented := contextGraftInstalled_context_rep d v4 c parent side sibling n l r addr cidr pid p
    hb hbelow hr hn hvfocus ha hbit hstop
  have htree := congrArg InsertResult.tree
    (context_graft_insertFresh c parent side sibling n l r (rootWidth v4) d.nextNode addr cidr pid hf hb hlt hm hbit)
  dsimp only at htree
  rw [← htree] at represented
  exact ⟨h.2, graftChildInstalled_below d v4 parent.id _ n.id _ addr cidr pid p hbelow
      (hbelow _ _ hparent) (hbelow _ _ hfocus.1), hmeta.2.1, represented,
    Tree.insertFresh_valid hv ha hc d.nextNode pid,
    Tree.insertFresh_nodeIds_nodup hn (hr.ids_below hbelow) (rootWidth v4) addr cidr pid,
    fun h => Tree.insertFresh_compressed h (rootWidth v4) d.nextNode addr cidr pid,
    hmeta.1, hmeta.2.2.1, hmeta.2.2.2,
    contextGraftInstalled_other_rep d v4 _ parent side sibling n l r addr cidr pid p hb hbelow hlocal other ho⟩

end Leanux.Proofs.WG.AllowedIps
