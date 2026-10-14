import Leanux.Proofs.WG.AllowedIps.InsertionCases

/-! Complete insertion dispatch from the original total placement traversal.
Input premises describe the represented store, never the desired insertion
result. Normal allocation refusals retain their exact source endpoints. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux

/-- Structural consequences shared by every successful insertion case. -/
structure Inserted (d out : WG.Device) (v4 : Bool) (t other : Tree)
    (addr cidr pid : Nat) : Prop where
  below : NodesBelow out
  root : rootValue out v4 = (t.insertFresh (rootWidth v4) d.nextNode addr cidr pid).tree.root
  rep : RepAt out.nodes (rootWidth v4) (rootSlot v4)
    (t.insertFresh (rootWidth v4) d.nextNode addr cidr pid).tree
  frontier : out.nextNode = d.nextNode + (t.insertFresh (rootWidth v4) d.nextNode addr cidr pid).allocations
  seq : out.peerAllowedips.seq = d.peerAllowedips.seq
  otherRoot : rootValue out (!v4) = rootValue d (!v4)
  otherRep : RepAt out.nodes (rootWidth (!v4)) (rootSlot (!v4)) other

/-- Classification concerns normal returns only. A refused record remains a
Stop, distinct from either normal allocator-refusal endpoint. -/
def AddOutcome (k after : Kernel) (d : WG.Device) (v4 : Bool) (t other : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) (ret : Int) : Prop :=
  (ret = -ENOMEM ∧ after = k) ∨
  (ret = -ENOMEM ∧ (t.insertFresh (rootWidth v4) d.nextNode addr cidr pid).allocations = 2 ∧
    after = { k with wg := some (graftRolledBack d (rootWidth v4) addr cidr pid p) }) ∨
  (ret = 0 ∧ ∃ out, after = { k with wg := some out } ∧ Inserted d out v4 t other addr cidr pid)

theorem Context.last_gap (c : Context) (hc : c ≠ .here) (hf : c.Follows width addr cidr) :
    ∃ (outer : Context) (parent : NodeData) (side : Nat) (sibling : Tree), side < 2 ∧ c = outer.append (gapContext parent side sibling) ∧
      outer.Follows width addr cidr ∧ parent.cidr < cidr ∧
      prefixBits width parent.cidr parent.addr = prefixBits width parent.cidr addr ∧
      bit width parent.cidr addr = side := by
  obtain ⟨outer, parent, l, r, side, hb, he⟩ := c.last_edge hc
  subst c
  obtain ⟨ho, hi⟩ := (Context.follows_append_iff _ _).mp hf
  have hcases : side = 0 ∨ side = 1 := by omega
  rcases hcases with rfl | rfl
  · exact ⟨outer, parent, 0, r, by omega, rfl, ho, hi.1, hi.2.1, hi.2.2.1⟩
  · exact ⟨outer, parent, 1, l, by omega, rfl, ho, hi.1, hi.2.1, hi.2.2.1⟩

theorem add_empty_outcome (w w' : World) (d : WG.Device) (hd : w.k.wg = some d)
    (v4 : Bool) (addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (he : rootValue d v4 = none) (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
    (hb : NodesBelow d) (other : Tree)
    (ho : RepAt d.nodes (rootWidth (!v4)) (rootSlot (!v4)) other) (ret : Int)
    (hrun : (WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w = .ok (ret, w')) :
    AddOutcome w.k w'.k d v4 .empty other addr cidr pid p ret := by
  have h := case_add_empty_root_correct w w' d hd v4 addr cidr pid p hp he ha hc hb other ho ret hrun
  rcases h with hf | ⟨hz, hk, hbelow, hroot, hrep, _, hother, horep⟩
  · exact .inl hf
  · refine .inr (.inr ⟨hz, _, hk, hbelow, hroot, hrep, ?_, ?_, hother, horep⟩)
    · rfl
    · exact emptyInstalled_seq d v4 addr cidr pid p

theorem add_gap_outcome (w w' : World) (d : WG.Device) (hd : w.k.wg = some d)
    (v4 : Bool) (c : Context) (n : NodeData) (side : Nat) (sibling : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (hroot : rootValue d v4 = (c.plug (Tree.fork n side .empty sibling)).root)
    (hb : side < 2) (hbelow : NodesBelow d)
    (hn : (c.plug (Tree.fork n side .empty sibling)).nodeIds.Nodup)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (c.plug (Tree.fork n side .empty sibling)))
    (hv : (c.plug (Tree.fork n side .empty sibling)).Valid (rootWidth v4))
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
    (hf : c.Follows (rootWidth v4) addr cidr) (hlt : n.cidr < cidr)
    (hm : prefixBits (rootWidth v4) n.cidr n.addr = prefixBits (rootWidth v4) n.cidr addr)
    (hbit : bit (rootWidth v4) n.cidr addr = side)
    (other : Tree) (ho : RepAt d.nodes (rootWidth (!v4)) (rootSlot (!v4)) other) (ret : Int)
    (hrun : (WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w = .ok (ret, w')) :
    AddOutcome w.k w'.k d v4 (c.plug (Tree.fork n side .empty sibling)) other addr cidr pid p ret := by
  have h := case_add_context_empty_child_correct w w' d hd v4 c n side sibling addr cidr pid p hp
    hroot hb hbelow hn hr hv ha hc hf hlt hm hbit other ho ret hrun
  rcases h with hfail | ⟨hz, hk, hb', hroot', hr', _, _, hnext, hseq, hroots, ho'⟩
  · exact .inl hfail
  · refine .inr (.inr ⟨hz, _, hk, hb', hroot', hr', ?_, hseq, hroots _, ho'⟩)
    rw [context_gap_insertFresh c n side sibling (rootWidth v4) d.nextNode addr cidr pid hf hb hlt hm hbit]
    exact hnext

theorem add_exact_outcome (w w' : World) (d : WG.Device) (hd : w.k.wg = some d)
    (v4 : Bool) (c : Context) (n : NodeData) (l r : Tree) (addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p)
    (hroot : rootValue d v4 = (c.plug (.node n l r)).root) (hbelow : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (c.plug (.node n l r)))
    (hv : (c.plug (.node n l r)).Valid (rootWidth v4))
    (hnodup : (c.plug (.node n l r)).nodeIds.Nodup)
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
    (hf : c.Follows (rootWidth v4) addr cidr) (hn : n.cidr = cidr)
    (hm : prefixBits (rootWidth v4) n.cidr n.addr = prefixBits (rootWidth v4) n.cidr addr)
    (other : Tree) (ho : RepAt d.nodes (rootWidth (!v4)) (rootSlot (!v4)) other) (ret : Int)
    (hrun : (WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w = .ok (ret, w')) :
    AddOutcome w.k w'.k d v4 (c.plug (.node n l r)) other addr cidr pid p ret := by
  obtain ⟨v, he, hk, hroot', hr', _, _, _, halloc, hnext, hseq, hroots, ho', _, _, _, hb⟩ :=
    case_add_context_exact_correct w d hd v4 c n l r addr cidr pid p hp hroot hr hv hnodup ha hc hf hn hm other ho
  rw [hrun] at he
  cases he
  refine .inr (.inr ⟨rfl, _, hk, hb hbelow, hroot', hr', ?_, hseq, hroots _, ho'⟩)
  rw [halloc, Nat.add_zero]
  exact hnext

theorem add_root_graft_outcome (w w' : World) (d : WG.Device) (hd : w.k.wg = some d)
    (v4 : Bool) (n : NodeData) (l r : Tree) (addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (hroot : rootValue d v4 = some n.id) (hb : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (.node n l r))
    (hn : (Tree.node n l r).nodeIds.Nodup) (hv : (Tree.node n l r).Valid (rootWidth v4))
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
    (hstop : ¬ (n.cidr ≤ cidr ∧ prefixBits (rootWidth v4) n.cidr n.addr = prefixBits (rootWidth v4) n.cidr addr))
    (other : Tree) (ho : RepAt d.nodes (rootWidth (!v4)) (rootSlot (!v4)) other) (ret : Int)
    (hrun : (WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w = .ok (ret, w')) :
    AddOutcome w.k w'.k d v4 (.node n l r) other addr cidr pid p ret := by
  have h := case_add_root_graft_endpoints w w' d hd v4 n l r addr cidr pid p hp hroot hb hr hv ha hc hstop ret hrun
  rcases h with hf | ⟨hf, hs, hk⟩ | ⟨hz, _⟩
  · exact .inl hf
  · refine .inr (.inl ⟨hf, ?_, hk⟩)
    rw [root_graft_insertFresh _ _ _ _ _ _ _ _ hstop]
    simp [graft, hs]
  · subst ret
    obtain ⟨hk, hb', hroot', hr', _, _, _, hnext, hother, hseq, ho'⟩ :=
      case_add_root_graft_correct w w' d hd v4 n l r addr cidr pid p hp hroot hb hr hn hv ha hc hstop other ho hrun
    exact .inr (.inr ⟨rfl, _, hk, hb', hroot', hr', hnext, hseq, hother, ho'⟩)

theorem add_deep_graft_outcome (w w' : World) (d : WG.Device) (hd : w.k.wg = some d)
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
    (other : Tree) (ho : RepAt d.nodes (rootWidth (!v4)) (rootSlot (!v4)) other) (ret : Int)
    (hrun : (WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w = .ok (ret, w')) :
    AddOutcome w.k w'.k d v4 (c.plug (Tree.fork parent side (.node n l r) sibling)) other addr cidr pid p ret := by
  have h := case_add_context_graft_endpoints w w' d hd v4 c parent side sibling n l r addr cidr pid p hp
    hroot hb hbelow hr hv hn ha hc hf hlt hm hbit hstop ret hrun
  rcases h with hfail | ⟨hfail, hs, hk⟩ | ⟨hz, _⟩
  · exact .inl hfail
  · refine .inr (.inl ⟨hfail, ?_, hk⟩)
    rw [context_graft_insertFresh c parent side sibling n l r (rootWidth v4) d.nextNode addr cidr pid hf hb hlt hm hbit]
    dsimp only
    rw [root_graft_insertFresh _ _ _ _ _ _ _ _ hstop]
    simp [graft, hs]
  · subst ret
    obtain ⟨hk, hb', hroot', hr', _, _, _, hnext, hother, hseq, ho'⟩ :=
      case_add_context_graft_correct w w' d hd v4 c parent side sibling n l r addr cidr pid p hp
        hroot hb hbelow hr hv hn ha hc hf hlt hm hbit hstop other ho hrun
    exact .inr (.inr ⟨rfl, _, hk, hb', hroot', hr', hnext, hseq, hother, ho'⟩)

/-- Every normal original add return is classified by deriving its structural
case from original nodePlacement. No path, exactness or stopping predicate is
required of the caller. -/
theorem add_outcome (w w' : World) (d : WG.Device) (hd : w.k.wg = some d)
    (v4 : Bool) (t other : Tree) (addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (hroot : rootValue d v4 = t.root)
    (hbelow : NodesBelow d) (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) t)
    (hv : t.Valid (rootWidth v4)) (hn : t.nodeIds.Nodup)
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
    (ho : RepAt d.nodes (rootWidth (!v4)) (rootSlot (!v4)) other) (ret : Int)
    (hrun : (WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w = .ok (ret, w')) :
    AddOutcome w.k w'.k d v4 t other addr cidr pid p ret := by
  have hw : rootWidth v4 = 32 ∨ rootWidth v4 = 128 := by cases v4 <;> simp [rootWidth]
  obtain ⟨result, _, _, _, c, u, ht, hf, hend⟩ :=
    nodePlacement_run w d (rootWidth v4) addr cidr hw ha hc hd t (rootSlot v4) hr hv
  subst t
  cases u with
  | empty =>
    by_cases he : c = .here
    · subst c
      exact add_empty_outcome w w' d hd v4 addr cidr pid p hp hroot ha hc hbelow other ho ret hrun
    · obtain ⟨outer, parent, side, sibling, hb, heq, hf', hlt, hm, hbit⟩ := c.last_gap he hf
      subst c
      simp only [Context.plug_append, gapContext_plug] at hroot hr hv hn ⊢
      exact add_gap_outcome w w' d hd v4 outer parent side sibling addr cidr pid p hp
        hroot hb hbelow hn hr hv ha hc hf' hlt hm hbit other ho ret hrun
  | node n l r =>
    have he : (n.cidr = cidr ∧ prefixBits (rootWidth v4) n.cidr n.addr = prefixBits (rootWidth v4) n.cidr addr) ∨
        ¬ (n.cidr ≤ cidr ∧ prefixBits (rootWidth v4) n.cidr n.addr = prefixBits (rootWidth v4) n.cidr addr) := by
      rcases hend with ⟨hlt, _⟩ | ⟨_, hmiss, _⟩ | ⟨heq, hm, _⟩
      · exact .inr (fun h => by omega)
      · exact .inr (fun h => hmiss h.2)
      · exact .inl ⟨heq, hm⟩
    rcases he with ⟨heq, hm⟩ | hstop
    · exact add_exact_outcome w w' d hd v4 c n l r addr cidr pid p hp hroot hbelow
        hr hv hn ha hc hf heq hm other ho ret hrun
    · by_cases he : c = .here
      · subst c
        exact add_root_graft_outcome w w' d hd v4 n l r addr cidr pid p hp hroot hbelow
          hr hn hv ha hc hstop other ho ret hrun
      · obtain ⟨outer, parent, side, sibling, hb, heq, hf', hlt, hm, hbit⟩ := c.last_gap he hf
        subst c
        simp only [Context.plug_append, gapContext_plug] at hroot hr hv hn ⊢
        exact add_deep_graft_outcome w w' d hd v4 outer parent side sibling n l r addr cidr pid p hp
          hroot hb hbelow hr hv hn ha hc hf' hlt hm hbit hstop other ho ret hrun

/-- Successful insertion carries the original Kernel endpoint and the actual
selected root, with independently proved pure validity, compression and IDs. -/
theorem add_success (w w' : World) (d : WG.Device) (hd : w.k.wg = some d)
    (v4 : Bool) (t other : Tree) (addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (hroot : rootValue d v4 = t.root)
    (hbelow : NodesBelow d) (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) t)
    (hv : t.Valid (rootWidth v4)) (hn : t.nodeIds.Nodup)
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
    (ho : RepAt d.nodes (rootWidth (!v4)) (rootSlot (!v4)) other)
    (hrun : (WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w = .ok (0, w')) :
    let inserted := t.insertFresh (rootWidth v4) d.nextNode addr cidr pid
    ∃ out, w'.k = { w.k with wg := some out } ∧ Inserted d out v4 t other addr cidr pid ∧
      inserted.tree.Valid (rootWidth v4) ∧ inserted.tree.nodeIds.Nodup ∧
      (t.Compressed → inserted.tree.Compressed) := by
  have outcome := add_outcome w w' d hd v4 t other addr cidr pid p hp hroot hbelow hr hv hn ha hc ho 0 hrun
  rcases outcome with hf | hf | ⟨_, out, hk, hs⟩
  · simp [ENOMEM] at hf
  · simp [ENOMEM] at hf
  exact ⟨out, hk, hs, Tree.insertFresh_valid hv ha hc d.nextNode pid,
    Tree.insertFresh_nodeIds_nodup hn (hr.ids_below hbelow) (rootWidth v4) addr cidr pid,
    fun h => Tree.insertFresh_compressed h (rootWidth v4) d.nextNode addr cidr pid⟩

theorem add_lookup (w w' : World) (d : WG.Device) (hd : w.k.wg = some d)
    (v4 : Bool) (t : Tree) (addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (hroot : rootValue d v4 = t.root)
    (hbelow : NodesBelow d) (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) t)
    (hv : t.Valid (rootWidth v4)) (hn : t.nodeIds.Nodup)
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
    (key : Nat) (hk : key < 2 ^ rootWidth v4)
    (hrun : (WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w = .ok (0, w')) :
    let inserted := t.insertFresh (rootWidth v4) d.nextNode addr cidr pid
    ∃ out final, w'.k.wg = some out ∧
      (WG.findNode (rootValue out v4) (rootWidth v4) key).run w' =
        .ok ((inserted.tree.lookup (rootWidth v4) key).map Entry.id, final) ∧
      Winner (rootWidth v4) key
        (inserted.binding :: t.entries.filter
          (fun e => e.prefixKey (rootWidth v4) != (cidr, prefixBits (rootWidth v4) cidr addr)))
        (inserted.tree.lookup (rootWidth v4) key) ∧ final.k = w'.k := by
  obtain ⟨out, hkernel, hs, hvalid, _⟩ :=
    add_success w w' d hd v4 t .empty addr cidr pid p hp hroot hbelow hr hv hn ha hc trivial hrun
  have hdev : w'.k.wg = some out := by rw [hkernel]
  have hw : rootWidth v4 = 32 ∨ rootWidth v4 = 128 := by cases v4 <;> simp [rootWidth]
  obtain ⟨final, he, hframe⟩ := findNode_run w' out (rootWidth v4) key hw hk hdev
    (t.insertFresh (rootWidth v4) d.nextNode addr cidr pid).tree (rootSlot v4) hs.rep hvalid
  refine ⟨out, final, hdev, ?_, Tree.insertFresh_lookup_spec hv ha hc d.nextNode pid key, hframe⟩
  simpa only [hs.root, Tree.lookupId] using he

/-- The wrapper's sequence advance precedes every add branch, including either
normal allocation refusal. The outcome is based on that bumped input Kernel. -/
theorem insert_outcome (w w' : World) (d : WG.Device) (hd : w.k.wg = some d)
    (family : Nat) (t other : Tree) (addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (hroot : rootValue d (family == 4) = t.root)
    (hbelow : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth (family == 4)) (rootSlot (family == 4)) t)
    (hv : t.Valid (rootWidth (family == 4))) (hn : t.nodeIds.Nodup)
    (ha : addr < 2 ^ rootWidth (family == 4)) (hc : cidr ≤ rootWidth (family == 4))
    (ho : RepAt d.nodes (rootWidth (!(family == 4))) (rootSlot (!(family == 4))) other)
    (ret : Int) (hrun : (WG.insert family addr cidr pid).run w = .ok (ret, w')) :
    AddOutcome { w.k with wg := some (bumpSeq d) } w'.k (bumpSeq d) (family == 4)
      t other addr cidr pid p ret := by
  rw [insert_run_bump w d hd family addr cidr pid] at hrun
  exact add_outcome { w with k := { w.k with wg := some (bumpSeq d) } } w' (bumpSeq d) rfl
    (family == 4) t other addr cidr pid p hp hroot hbelow hr hv hn ha hc ho ret hrun

theorem insert_success (w w' : World) (d : WG.Device) (hd : w.k.wg = some d)
    (family : Nat) (t other : Tree) (addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (hroot : rootValue d (family == 4) = t.root)
    (hbelow : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth (family == 4)) (rootSlot (family == 4)) t)
    (hv : t.Valid (rootWidth (family == 4))) (hn : t.nodeIds.Nodup)
    (ha : addr < 2 ^ rootWidth (family == 4)) (hc : cidr ≤ rootWidth (family == 4))
    (ho : RepAt d.nodes (rootWidth (!(family == 4))) (rootSlot (!(family == 4))) other)
    (hrun : (WG.insert family addr cidr pid).run w = .ok (0, w')) :
    let inserted := t.insertFresh (rootWidth (family == 4)) d.nextNode addr cidr pid
    ∃ out, w'.k = { w.k with wg := some out } ∧
      out.peerAllowedips.seq = d.peerAllowedips.seq + 1 ∧
      Inserted (bumpSeq d) out (family == 4) t other addr cidr pid ∧
      inserted.tree.Valid (rootWidth (family == 4)) ∧ inserted.tree.nodeIds.Nodup ∧
      (t.Compressed → inserted.tree.Compressed) := by
  rw [insert_run_bump w d hd family addr cidr pid] at hrun
  obtain ⟨out, hk, hs, hv', hn', hcomp⟩ :=
    add_success { w with k := { w.k with wg := some (bumpSeq d) } } w' (bumpSeq d) rfl
      (family == 4) t other addr cidr pid p hp hroot hbelow hr hv hn ha hc ho hrun
  exact ⟨out, hk, hs.seq, hs, hv', hn', hcomp⟩

theorem insert_lookup (w w' : World) (d : WG.Device) (hd : w.k.wg = some d)
    (family : Nat) (t : Tree) (addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (hroot : rootValue d (family == 4) = t.root)
    (hbelow : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth (family == 4)) (rootSlot (family == 4)) t)
    (hv : t.Valid (rootWidth (family == 4))) (hn : t.nodeIds.Nodup)
    (ha : addr < 2 ^ rootWidth (family == 4)) (hc : cidr ≤ rootWidth (family == 4))
    (key : Nat) (hk : key < 2 ^ rootWidth (family == 4))
    (hrun : (WG.insert family addr cidr pid).run w = .ok (0, w')) :
    let v4 := family == 4
    let inserted := t.insertFresh (rootWidth v4) d.nextNode addr cidr pid
    ∃ out final, w'.k.wg = some out ∧
      (WG.findNode (rootValue out v4) (rootWidth v4) key).run w' =
        .ok ((inserted.tree.lookup (rootWidth v4) key).map Entry.id, final) ∧
      Winner (rootWidth v4) key
        (inserted.binding :: t.entries.filter
          (fun e => e.prefixKey (rootWidth v4) != (cidr, prefixBits (rootWidth v4) cidr addr)))
        (inserted.tree.lookup (rootWidth v4) key) ∧ final.k = w'.k := by
  rw [insert_run_bump w d hd family addr cidr pid] at hrun
  exact add_lookup { w with k := { w.k with wg := some (bumpSeq d) } } w' (bumpSeq d) rfl
    (family == 4) t addr cidr pid p hp hroot hbelow hr hv hn ha hc key hk hrun

/-- A normal allocator refusal preserves both root values and all node lookups.
The only frontier/list alternatives are no change, or one consumed identifier
and removal of that scalar identifier from every resident peer list. -/
theorem add_refusal (w w' : World) (d : WG.Device) (hd : w.k.wg = some d)
    (v4 : Bool) (t : Tree) (addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (hroot : rootValue d v4 = t.root)
    (hbelow : NodesBelow d) (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) t)
    (hv : t.Valid (rootWidth v4)) (hn : t.nodeIds.Nodup)
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
    (hrun : (WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w = .ok (-ENOMEM, w')) :
    ∃ out, w'.k = { w.k with wg := some out } ∧ NodesBelow out ∧
      out.peerAllowedips.seq = d.peerAllowedips.seq ∧
      (∀ f, rootValue out f = rootValue d f) ∧
      (∀ id : Nat, out.nodes[id]? = d.nodes[id]?) ∧
      ((out.nextNode = d.nextNode ∧ ∀ q : Nat, out.peers[q]? = d.peers[q]?) ∨
        (out.nextNode = d.nextNode + 1 ∧
          (t.insertFresh (rootWidth v4) d.nextNode addr cidr pid).allocations = 2 ∧
          ∀ q : Nat, out.peers[q]? = (d.peers[q]?).map (unlist d.nextNode))) := by
  have outcome := add_outcome w w' d hd v4 t .empty addr cidr pid p hp hroot hbelow hr hv hn ha hc trivial (-ENOMEM) hrun
  rcases outcome with ⟨_, hk⟩ | ⟨_, halloc, hk⟩ | ⟨hz, _⟩
  · refine ⟨d, ?_, hbelow, rfl, fun _ => rfl, fun _ => rfl, .inl ⟨rfl, fun _ => rfl⟩⟩
    rw [hk]
    rw [← hd]
  · refine ⟨_, hk, graftRolledBack_below d (rootWidth v4) addr cidr pid p hbelow,
      ?_, ?_, graftRolledBack_nodes d (rootWidth v4) addr cidr pid p hbelow,
      .inr ⟨?_, halloc, graftRolledBack_peer d (rootWidth v4) addr cidr pid p hp⟩⟩
    · simp only [graftRolledBack, unlisted, graftListed, allocated]
    · intro f
      simp only [graftRolledBack, unlisted, graftListed, allocated, rootValue]
    · simp only [graftRolledBack, unlisted, graftListed, allocated]
  · simp [ENOMEM] at hz

end Leanux.Proofs.WG.AllowedIps
