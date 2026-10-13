import Leanux.Proofs.WG.AllowedIps.GraftLink

/-! Original nonempty graft insertion below a represented parent. The exact
source suffix is shared with selected-root grafting. -/
set_option pp.structureInstances false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Std.Do Leanux.Proofs.Framing

theorem Context.stopped_result (c observed : Context) (n : NodeData) (l r u : Tree) (previous : Option Nat)
    (hstop : ¬ (n.cidr ≤ cidr ∧ prefixBits width n.cidr n.addr = prefixBits width n.cidr key))
    (hf : c.Follows width key cidr) (ho : observed.Follows width key cidr)
    (ht : c.plug (.node n l r) = observed.plug u)
    (he : PlacementEnd width key cidr (observed.lastParent previous) u result) :
    result = (c.lastParent previous, false) := by
  induction c generalizing observed u previous with
  | here =>
    cases observed with
    | here =>
      change Tree.node n l r = u at ht
      subst u
      rcases he with ⟨_, hret⟩ | ⟨_, _, hret⟩ | ⟨heq, hm, _⟩
      · exact hret
      · exact hret
      · exact False.elim (hstop ⟨by omega, hm⟩)
    | left m inner right =>
      have heq := (Tree.node.inj ht).1
      subst m
      exact False.elim (hstop ⟨Nat.le_of_lt ho.1, ho.2.1⟩)
    | right m left inner =>
      have heq := (Tree.node.inj ht).1
      subst m
      exact False.elim (hstop ⟨Nat.le_of_lt ho.1, ho.2.1⟩)
  | left a c sibling ih =>
    cases observed with
    | here =>
      change Tree.node a (c.plug (.node n l r)) sibling = u at ht
      subst u
      rcases he with ⟨hlt, _⟩ | ⟨_, hm, _⟩ | ⟨heq, _, _⟩
      · have := hf.1; omega
      · exact False.elim (hm hf.2.1)
      · have := hf.1; omega
    | left m inner right =>
      obtain ⟨hn, hl, hr⟩ := Tree.node.inj ht
      subst m
      exact ih inner u (some a.id) hf.2.2.2 ho.2.2.2 hl he
    | right m left inner =>
      have hn := (Tree.node.inj ht).1
      subst m
      have h0 := hf.2.2.1
      have h1 := ho.2.2.1
      omega
  | right a sibling c ih =>
    cases observed with
    | here =>
      change Tree.node a sibling (c.plug (.node n l r)) = u at ht
      subst u
      rcases he with ⟨hlt, _⟩ | ⟨_, hm, _⟩ | ⟨heq, _, _⟩
      · have := hf.1; omega
      · exact False.elim (hm hf.2.1)
      · have := hf.1; omega
    | left m inner right =>
      have hn := (Tree.node.inj ht).1
      subst m
      have h1 := hf.2.2.1
      have h0 := ho.2.2.1
      omega
    | right m left inner =>
      obtain ⟨hn, hl, hr⟩ := Tree.node.inj ht
      subst m
      exact ih inner u (some a.id) hf.2.2.2 ho.2.2.2 hr he


theorem nodePlacement_context_stopped_wp (k : Kernel) (d : WG.Device) (hd : k.wg = some d)
    (width key cidr : Nat) (hw : width = 32 ∨ width = 128) (hk : key < 2 ^ width)
    (hc : cidr ≤ width) (base : WG.Slot) (c : Context) (n : NodeData) (l r : Tree)
    (hr : RepAt d.nodes width base (c.plug (.node n l r)))
    (hv : (c.plug (.node n l r)).Valid width) (hf : c.Follows width key cidr)
    (hstop : ¬ (n.cidr ≤ cidr ∧ prefixBits width n.cidr n.addr = prefixBits width n.cidr key)) :
    ⦃fun w => ⌜w.k = k⌝⦄ WG.nodePlacement (c.plug (.node n l r)).root key cidr width
    ⦃⇓ x w => ⌜x = (c.lastParent none, false) ∧ w.k = k⌝⦄ := by
  apply (total_iff_run _ _ _).mpr
  intro w hkw
  obtain ⟨x, v, he, hframe, observed, u, ht, ho, hend⟩ := nodePlacement_run w d width key cidr hw hk hc
    (hkw ▸ hd) (c.plug (.node n l r)) base hr hv
  exact ⟨x, v, he, c.stopped_result observed n l r u none hstop hf ho ht hend, hframe.trans hkw⟩

theorem bitAt_some_wp (k : Kernel) (pn : WG.AipNode) (side id : Nat)
    (hbit : pn.bit[side]? = some (some id)) :
    ⦃fun w => ⌜w.k = k⌝⦄ pn.bitAt side
    ⦃⇓ x w => ⌜x = some id ∧ w.k = k⌝⦄ := by
  apply (total_iff_run _ _ _).mpr
  intro w hkw
  exact ⟨some id, w, by simp [WG.AipNode.bitAt, hbit], rfl, hkw⟩

theorem graftTail_child_wp (k : Kernel) (d : WG.Device) (v4 : Bool)
    (parent : Nat) (pn : WG.AipNode) (id : Nat) (old : WG.AipNode)
    (addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.nodes[parent]? = some pn) (hn : d.nodes[id]? = some old)
    (hbelow : NodesBelow d) (hne : parent ≠ id) (hcidr : pn.cidr < pn.bitlen)
    (hs : min cidr (common (rootWidth v4) old.bits addr) < rootWidth v4) :
    ⦃fun w => ⌜w.k = { k with wg := some (graftListed d (rootWidth v4) addr cidr pid p) }⌝⦄
      graftTail (rootSlot v4) (rootWidth v4) addr cidr (some parent) d.nextNode id
    ⦃⇓? result w => ⌜(result = -ENOMEM ∧ w.k = k) ∨
      (result = -ENOMEM ∧ min cidr (common (rootWidth v4) old.bits addr) ≠ cidr ∧
        w.k = { k with wg := some (graftRolledBack d (rootWidth v4) addr cidr pid p) }) ∨
      (result = 0 ∧ w.k = { k with wg := some (graftChildInstalled d v4 parent pn id old addr cidr pid p) })⌝⦄ := by
  have hfp : d.nextNode ≠ parent := Nat.ne_of_gt (hbelow _ _ hp)
  have hmp : d.nextNode + 1 ≠ parent := Nat.ne_of_gt (Nat.lt_succ_of_lt (hbelow _ _ hp))
  have hfi : d.nextNode ≠ id := Nat.ne_of_gt (hbelow _ _ hn)
  let one := graftOneReady d v4 id old addr cidr pid p
  let two := graftTwoReady d v4 id old addr cidr pid (min cidr (common (rootWidth v4) old.bits addr)) p
  have hp1 : one.nodes[parent]? = some pn := by
    simp [one, graftOneReady, connectedChild, graftListed, allocated, Std.TreeMap.getElem?_insert, hfp, Ne.symm hne, hp]
  have hn1 : one.nodes[d.nextNode]? = some (graftOneHead v4 id old addr cidr pid) := by
    simp [one, graftOneReady, graftOneHead, connectedChild]
  have hp2 : two.nodes[parent]? = some pn := by
    simp [two, graftTwoReady, connectedChild, graftListed, allocated, Std.TreeMap.getElem?_insert, hfp, hmp, Ne.symm hne, hp]
  have hn2 : two.nodes[d.nextNode+1]? = some (graftTwoHead d v4 id old addr (min cidr (common (rootWidth v4) old.bits addr))) := by
    simp [two, graftTwoReady, graftTwoHead, connectedChild]
  have finish1 := finishGraft_child_wp { k with wg := some one } one rfl .addNewnodeAtRoot
    (rootSlot v4) parent d.nextNode pn _ hp1 hn1 hfp hcidr
  have finish2 := finishGraft_child_wp { k with wg := some two } two rfl .addIntermediateAtRoot
    (rootSlot v4) parent (d.nextNode+1) pn _ hp2 hn2 hmp hcidr
  have tail := graftTail_wp k d v4 id old addr cidr pid p (some parent) hn (hbelow _ _ hn) hs
    (graftOneChild d v4 parent pn id old addr cidr pid p)
    (graftTwoChild d v4 parent pn id old addr cidr pid (min cidr (common (rootWidth v4) old.bits addr)) p)
    (by simpa [one, graftOneChild, graftOneReady, graftOneHead, WG.newNode] using finish1)
    (by simpa [two, graftTwoChild, graftTwoReady, graftTwoHead, WG.newNode] using finish2)
  exact tail

/-- The original nonempty child path, retaining the final original
`chooseAndConnectNode` call and both normal allocation-refusal endpoints. -/
theorem add_placed_child_graft_wp (k : Kernel) (d : WG.Device) (hd : k.wg = some d)
    (v4 : Bool) (trie parent : Nat) (pn : WG.AipNode) (id : Nat) (old : WG.AipNode)
    (addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (hroot : rootValue d v4 = some trie) (hbelow : NodesBelow d)
    (hnp : d.nodes[parent]? = some pn) (hno : d.nodes[id]? = some old)
    (hne : parent ≠ id) (hc : cidr ≤ rootWidth v4) (hpc : pn.cidr < pn.bitlen)
    (hchild : pn.bit[bit pn.bitlen pn.cidr addr]? = some (some id))
    (hs : min cidr (common (rootWidth v4) old.bits addr) < rootWidth v4)
    (hplacement : ⦃fun w => ⌜w.k = k⌝⦄ WG.nodePlacement (some trie) addr cidr (rootWidth v4)
      ⦃⇓ result w => ⌜result = (some parent, false) ∧ w.k = k⌝⦄) :
    ⦃fun w => ⌜w.k = k⌝⦄ WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)
    ⦃⇓? result w => ⌜(result = -ENOMEM ∧ w.k = k) ∨
      (result = -ENOMEM ∧ min cidr (common (rootWidth v4) old.bits addr) ≠ cidr ∧
        w.k = { k with wg := some (graftRolledBack d (rootWidth v4) addr cidr pid p) }) ∨
      (result = 0 ∧ w.k = { k with wg := some (graftChildInstalled d v4 parent pn id old addr cidr pid p) })⌝⦄ := by
  rw [← addWithTail_eq]
  have hgetRoot := slotGet_root_wp k d hd v4
  simp only [hroot] at hgetRoot
  have halloc := allocNode_wp k d hd .allocNode205 (WG.newNode addr cidr (rootWidth v4) (some pid))
  mvcgen [addWithTail, branchCmp, branch, hgetRoot, invariant]
  all_goals try dsimp only at *
  all_goals try simp_all
  all_goals try omega
  obtain ⟨hptr, hframe⟩ := (show _ = some trie ∧ _ = k from by assumption)
  cases hptr
  mvcgen [hplacement, branch, invariant]
  all_goals try dsimp only at *
  all_goals try simp_all
  obtain ⟨hplaced, hplacedFrame⟩ := (show _ = (some parent, false) ∧ _ = k from by assumption)
  cases hplaced
  mvcgen [halloc, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all
  obtain ⟨hnewId, hak⟩ := (show _ = d.nextNode ∧ _ =
    { k with wg := some (allocated d (WG.newNode addr cidr (rootWidth v4) (some pid))) } from by assumption)
  cases hnewId
  let da := allocated d (WG.newNode addr cidr (rootWidth v4) (some pid))
  let ka : Kernel := { k with wg := some da }
  have hlist := listAddTail_wp ka da rfl pid d.nextNode p hp
  mvcgen [hlist, branch, invariant]
  all_goals try dsimp only at *
  all_goals try simp_all
  intro hlisted
  let dl := graftListed d (rootWidth v4) addr cidr pid p
  let kl : Kernel := { k with wg := some dl }
  change _ = kl at hlisted
  have hfp : d.nextNode ≠ parent := Nat.ne_of_gt (hbelow parent pn hnp)
  have hnlisted : dl.nodes[parent]? = some pn := by
    simp [dl, graftListed, allocated, Std.TreeMap.getElem?_insert, hfp, hnp]
  have getter := getNode_wp kl dl parent pn rfl hnlisted
  mvcgen [getter]
  all_goals try (dsimp +zetaDelta only; exact hlisted)
  rename_i fetched
  intro currentGet hget hgetFrame
  subst fetched
  have choosing := choose_wp kl pn addr hpc
  mvcgen [choosing]
  all_goals try exact hgetFrame
  rename_i chosen
  intro currentChoose hchoose hchooseFrame
  subst chosen
  mvcgen [getter]
  all_goals try exact hchooseFrame
  rename_i fetchedAgain
  intro currentGetAgain hgetAgain hgetAgainFrame
  subst fetchedAgain
  have hbitAt := bitAt_some_wp kl pn (bit pn.bitlen pn.cidr addr) id hchild
  mvcgen [hbitAt, branch, invariant]
  all_goals try exact hgetAgainFrame
  all_goals try dsimp only at *
  all_goals try simp_all
  intro hdown hdownFrame
  have tail := graftTail_child_wp k d v4 parent pn id old addr cidr pid p hnp hno hbelow hne hpc hs
  mvcgen [tail]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

theorem add_context_graft_wp (k : Kernel) (d : WG.Device) (hd : k.wg = some d)
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
    (hstop : ¬ (n.cidr ≤ cidr ∧ prefixBits (rootWidth v4) n.cidr n.addr = prefixBits (rootWidth v4) n.cidr addr)) :
    ⦃fun w => ⌜w.k = k⌝⦄ WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)
    ⦃⇓? result w => ⌜(result = -ENOMEM ∧ w.k = k) ∨
      (result = -ENOMEM ∧ min cidr (common (rootWidth v4) n.addr addr) ≠ cidr ∧
        w.k = { k with wg := some (graftRolledBack d (rootWidth v4) addr cidr pid p) }) ∨
      (result = 0 ∧ w.k = { k with wg := some (contextGraftInstalled d v4
        (c.slot (rootSlot v4)) parent side sibling n l r addr cidr pid p) })⌝⦄ := by
  have hw : rootWidth v4 = 32 ∨ rootWidth v4 = 128 := by cases v4 <;> simp [rootWidth]
  have hpctx := hf.append (gapContext_follows parent side sibling hb hlt hm hbit)
  have hplacement := nodePlacement_context_stopped_wp k d hd (rootWidth v4) addr cidr hw ha hc
    (rootSlot v4) (c.append (gapContext parent side sibling)) n l r
    (by simpa only [Context.plug_append, gapContext_plug] using hr)
    (by simpa only [Context.plug_append, gapContext_plug] using hv) hpctx hstop
  have hlast : (gapContext parent side sibling).lastParent (c.lastParent none) = some parent.id := by
    unfold gapContext
    split <;> rfl
  simp only [Context.plug_append, gapContext_plug, Context.lastParent_append, hlast] at hplacement
  obtain ⟨trie, htrie⟩ : ∃ trie, (c.plug (Tree.fork parent side (.node n l r) sibling)).root = some trie := by
    cases c with
    | here => exact ⟨parent.id, Tree.fork_root parent side (.node n l r) sibling⟩
    | left a inner r => exact ⟨a.id, rfl⟩
    | right a l inner => exact ⟨a.id, rfl⟩
  rw [htrie] at hplacement
  obtain ⟨hparent, hfocus, _⟩ := fork_rep_parts hb (c.focus_rep _ _ hr)
  have hvlocal := c.focus_valid _ hv
  have hvfocus : (Tree.node n l r).Valid (rootWidth v4) := by
    have h := (gapContext parent side sibling).focus_valid (width := rootWidth v4) (.node n l r)
    exact h (by simpa only [gapContext_plug] using hvlocal)
  have hnlocal := (Tree.fork_nodeIds_perm parent side (.node n l r) sibling).nodup (c.focus_nodup _ hn)
  have hne : parent.id ≠ n.id := by
    intro he
    have hnot := (List.nodup_cons.mp hnlocal).1
    exact hnot (by simp [Tree.nodeIds, he])
  have bound := Nat.lt_of_lt_of_le (graftable_of_stopped hvfocus ha hstop) hvfocus.2.1
  apply add_placed_child_graft_wp k d hd v4 trie parent.id
    (forkNode (rootWidth v4) (c.slot (rootSlot v4)) parent side (.node n l r) sibling)
    n.id (encode (rootWidth v4) (.child parent.id side) n l r) addr cidr pid p hp
    (hroot.trans htrie) hbelow hparent hfocus.1 hne hc
    (by simp only [forkNode_cidr, forkNode_bitlen]; omega) ?_ bound hplacement
  have hcases : side = 0 ∨ side = 1 := by omega
  rcases hcases with rfl | rfl <;> simp [forkNode, encode, hbit, Tree.root]

end Leanux.Proofs.WG.AllowedIps
