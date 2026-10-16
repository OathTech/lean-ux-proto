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


theorem nodePlacement_context_stopped_wp (k : WG.AipStore)
    (width key cidr : Nat) (hw : width = 32 ∨ width = 128) (hk : key < 2 ^ width)
    (hc : cidr ≤ width) (base : WG.Slot) (c : Context) (n : NodeData) (l r : Tree)
    (hr : RepAt k.nodes width base (c.plug (.node n l r)))
    (hv : (c.plug (.node n l r)).Valid width) (hf : c.Follows width key cidr)
    (hstop : ¬ (n.cidr ≤ cidr ∧ prefixBits width n.cidr n.addr = prefixBits width n.cidr key)) :
    ⦃fun w => ⌜w = k⌝⦄ WG.nodePlacement (c.plug (.node n l r)).root key cidr width
    ⦃⇓ x w => ⌜x = (c.lastParent none, false) ∧ w = k⌝⦄ := by
  apply (total_iff_run_ambient _ _ _).mpr
  intro w ambient hkw
  obtain ⟨x, v, finalAmbient, he, hframe, observed, u, ht, ho, hend⟩ :=
    nodePlacement_run w ambient width key cidr hw hk hc
      (c.plug (.node n l r)) base (hkw ▸ hr) hv
  exact ⟨x, v, finalAmbient, he, c.stopped_result observed n l r u none hstop hf ho ht hend, hframe.trans hkw⟩

theorem bitAt_some_wp {σ : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] [MonadLiftT AmbientM (StateT σ m)]
    (k : σ) (pn : WG.AipNode) (side id : Nat)
    (hbit : pn.bit[side]? = some (some id)) :
    ⦃fun w => ⌜w = k⌝⦄ (pn.bitAt side : StateT σ m (Option Nat))
    ⦃⇓ x w => ⌜x = some id ∧ w = k⌝⦄ := by
  rw [show (pn.bitAt side : StateT σ m (Option Nat)) = pure (some id) from by
    simp [WG.AipNode.bitAt, hbit]]
  mvcgen

theorem graftTail_child_wp (k : WGWorld) (d : WG.Device) (v4 : Bool)
    (parent : Nat) (pn : WG.AipNode) (id : Nat) (old : WG.AipNode)
    (addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.nodes[parent]? = some pn) (hn : d.nodes[id]? = some old)
    (hbelow : NodesBelow d) (hne : parent ≠ id) (hcidr : pn.cidr < pn.bitlen)
    (hs : min cidr (common (rootWidth v4) old.bits addr) < rootWidth v4) :
    ⦃fun w => ⌜w = { k with dev := some (graftListed d (rootWidth v4) addr cidr pid p) }⌝⦄
      graftTail (rootSlot v4) (rootWidth v4) addr cidr (some parent) d.nextNode id
    ⦃⇓? result w => ⌜(result = -ENOMEM ∧ w = k) ∨
      (result = -ENOMEM ∧ min cidr (common (rootWidth v4) old.bits addr) ≠ cidr ∧
        w = { k with dev := some (graftRolledBack d (rootWidth v4) addr cidr pid p) }) ∨
      (result = 0 ∧ w = { k with dev := some (graftChildInstalled d v4 parent pn id old addr cidr pid p) })⌝⦄ := by
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
  have finish1 := finishGraft_child_wp { k with dev := some one } one rfl .addNewnodeAtRoot
    (rootSlot v4) parent d.nextNode pn _ hp1 hn1 hfp hcidr
  have finish2 := finishGraft_child_wp { k with dev := some two } two rfl .addIntermediateAtRoot
    (rootSlot v4) parent (d.nextNode+1) pn _ hp2 hn2 hmp hcidr
  have tail := graftTail_wp k d v4 id old addr cidr pid p (some parent) hn (hbelow _ _ hn) hs
    (graftOneChild d v4 parent pn id old addr cidr pid p)
    (graftTwoChild d v4 parent pn id old addr cidr pid (min cidr (common (rootWidth v4) old.bits addr)) p)
    (by simpa [one, graftOneChild, graftOneReady, graftOneHead, WG.newNode] using finish1)
    (by simpa [two, graftTwoChild, graftTwoReady, graftTwoHead, WG.newNode] using finish2)
  exact tail

/-- The original nonempty child path, retaining the final original
`chooseAndConnectNode` call and both normal allocation-refusal endpoints. -/
theorem add_placed_child_graft_wp (k : WGWorld) (d : WG.Device) (hd : k.dev = some d)
    (v4 : Bool) (trie parent : Nat) (pn : WG.AipNode) (id : Nat) (old : WG.AipNode)
    (addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (hroot : rootValue d v4 = some trie) (hbelow : NodesBelow d)
    (hnp : d.nodes[parent]? = some pn) (hno : d.nodes[id]? = some old)
    (hne : parent ≠ id) (hc : cidr ≤ rootWidth v4) (hpc : pn.cidr < pn.bitlen)
    (hchild : pn.bit[bit pn.bitlen pn.cidr addr]? = some (some id))
    (hs : min cidr (common (rootWidth v4) old.bits addr) < rootWidth v4)
    (hplacement : ⦃fun w => ⌜w = k⌝⦄ (MonadLift.monadLift (WG.nodePlacement (some trie) addr cidr (rootWidth v4)) : WG.M (Option Nat × Bool))
      ⦃⇓ result w => ⌜result = (some parent, false) ∧ w = k⌝⦄) :
    ⦃fun w => ⌜w = k⌝⦄ WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)
    ⦃⇓? result w => ⌜(result = -ENOMEM ∧ w = k) ∨
      (result = -ENOMEM ∧ min cidr (common (rootWidth v4) old.bits addr) ≠ cidr ∧
        w = { k with dev := some (graftRolledBack d (rootWidth v4) addr cidr pid p) }) ∨
      (result = 0 ∧ w = { k with dev := some (graftChildInstalled d v4 parent pn id old addr cidr pid p) })⌝⦄ := by
  let store (d : WG.Device) : WG.AipStore :=
    {nodes := d.nodes, nextNode := d.nextNode, trie := d.peerAllowedips}
  have read {α : Type} (g : WGWorld) (d : WG.Device) (hd : g.dev = some d)
      (a : WG.AipM α) (value : α)
      (h : ⦃fun s => ⌜s = store d⌝⦄ a ⦃⇓ x s => ⌜x = value ∧ s = store d⌝⦄) :
      ⦃fun w => ⌜w = g⌝⦄ (MonadLift.monadLift a : WG.M α)
      ⦃⇓ x w => ⌜x = value ∧ w = g⌝⦄ := by
    apply (total_iff_run_ambient _ _ _).mpr
    intro w ambient hw
    subst w
    obtain ⟨x, s, ambient', hr, hv, hs⟩ := (total_iff_run_ambient _ _ _).mp h _ ambient rfl
    subst s
    refine ⟨x, g, ambient', ?_, hv, rfl⟩
    change ((WG.liftAip a).run g).run ambient = _
    rw [liftAip_run, hd]
    simp only [store] at hr
    simp only [hr, Except.map]
    change Except.ok ((x, {g with dev := some d}), ambient') = _
    rw [← hd]
  have rootNative := slotGet_root_wp (store d) v4
  have rootValueEq : (if v4 then (store d).trie.root4 else (store d).trie.root6) = some trie := hroot
  simp only [rootValueEq] at rootNative
  have hgetRoot := read k d hd _ _ rootNative
  have halloc : ⦃fun w => ⌜w = k⌝⦄
      (MonadLift.monadLift (WG.allocNode .allocNode205 (WG.newNode addr cidr (rootWidth v4) (some pid))) : WG.M (Option Nat))
      ⦃⇓? result w => ⌜(result = none ∧ w = k) ∨
        (result = some d.nextNode ∧ w = { k with dev := some (allocated d (WG.newNode addr cidr (rootWidth v4) (some pid))) })⌝⦄ := by
    apply hoare_liftAip_of
    intro g d' hg hd'
    subst g
    have hdd : d' = d := Option.some.inj (hd'.symm.trans hd)
    subst d'
    apply hoare_consequence (allocNode_wp _ _ _)
    · intro s h; exact h
    · intro r s h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · left; refine ⟨rfl, ?_⟩
        change { k with dev := some d } = k
        rw [← hd]
      · right; simp [allocated]
  let leaf := WG.newNode addr cidr (rootWidth v4) (some pid)
  let da := allocated d leaf
  let ka : WGWorld := { k with dev := some da }
  have hlist := listAddTail_wp ka da rfl pid d.nextNode p hp
  let dl := { da with peers := da.peers.insert pid { p with allowedipsList := p.allowedipsList ++ [d.nextNode] } }
  let kl : WGWorld := { k with dev := some dl }
  have hfp : d.nextNode ≠ parent := Nat.ne_of_gt (hbelow parent pn hnp)
  have hnlisted : dl.nodes[parent]? = some pn := by
    simp [dl, da, allocated, Std.TreeMap.getElem?_insert, hfp, hnp]
  have getter := read kl dl rfl _ _ (getNode_wp (store dl) parent pn hnlisted)
  have choosing : ⦃fun w => ⌜w = kl⌝⦄ (WG.choose pn addr : WG.M Nat)
      ⦃⇓ x w => ⌜x = bit pn.bitlen pn.cidr addr ∧ w = kl⌝⦄ := by
    rw [choose_run pn addr hpc]
    mvcgen
  have hbitAt := bitAt_some_wp (m := AmbientM) kl pn (bit pn.bitlen pn.cidr addr) id hchild
  have tail := graftTail_child_wp k d v4 parent pn id old addr cidr pid p hnp hno hbelow hne hpc hs
  clear read rootNative
  rw [← addWithTail_eq]
  mvcgen [addWithTail, branchCmp, AmbientM.branchCmp, branch, AmbientM.branch, hgetRoot, invariant, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all
  all_goals try omega
  obtain ⟨hptr, hframe⟩ := (show _ = some trie ∧ _ = k from by assumption)
  cases hptr
  cases hframe
  mvcgen [hplacement, branch, AmbientM.branch, invariant, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all
  obtain ⟨hplaced, hplacedFrame⟩ := (show _ = (some parent, false) ∧ _ = k from by assumption)
  cases hplaced
  cases hplacedFrame
  mvcgen [halloc, branch, AmbientM.branch, invariant, AmbientM.invariant]
  all_goals try dsimp only at *
  all_goals
    obtain hcases := (show (_ = none ∧ _ = k) ∨
      (_ = some d.nextNode ∧ _ = { k with dev := some (allocated d (WG.newNode addr cidr (rootWidth v4) (some pid))) }) from by assumption)
    rcases hcases with ⟨hresult, hstate⟩ | ⟨hresult, hstate⟩
    all_goals try cases hresult
    all_goals try cases hstate
  all_goals clear hplacement halloc hgetRoot
  all_goals try simp_all
  all_goals try
    have heq := (show some d.nextNode = some _ from by assumption)
    cases Option.some.inj heq
  iterate 8
    all_goals try mvcgen [hlist, getter, choosing, hbitAt, tail,
      branch, AmbientM.branch, invariant, AmbientM.invariant]
    all_goals try dsimp only at *
    all_goals repeat intro
    all_goals try
      obtain ⟨rfl, rfl⟩ := (show _ = pn ∧ _ = kl from by assumption)
    all_goals try
      obtain ⟨rfl, rfl⟩ := (show _ = bit pn.bitlen pn.cidr addr ∧ _ = kl from by assumption)
    all_goals try
      obtain ⟨rfl, rfl⟩ := (show _ = some id ∧ _ = kl from by assumption)
    all_goals try simp_all
    all_goals try (simp_all only [ka, kl, dl, da, leaf])
  all_goals clear hlist getter choosing hbitAt tail
  all_goals simp_all [graftListed, allocated]

theorem add_context_graft_wp (k : WGWorld) (d : WG.Device) (hd : k.dev = some d)
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
    ⦃fun w => ⌜w = k⌝⦄ WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)
    ⦃⇓? result w => ⌜(result = -ENOMEM ∧ w = k) ∨
      (result = -ENOMEM ∧ min cidr (common (rootWidth v4) n.addr addr) ≠ cidr ∧
        w = { k with dev := some (graftRolledBack d (rootWidth v4) addr cidr pid p) }) ∨
      (result = 0 ∧ w = { k with dev := some (contextGraftInstalled d v4
        (c.slot (rootSlot v4)) parent side sibling n l r addr cidr pid p) })⌝⦄ := by
  have hw : rootWidth v4 = 32 ∨ rootWidth v4 = 128 := by cases v4 <;> simp [rootWidth]
  have hpctx := hf.append (gapContext_follows parent side sibling hb hlt hm hbit)
  let store : WG.AipStore := {nodes := d.nodes, nextNode := d.nextNode, trie := d.peerAllowedips}
  have nativePlacement := nodePlacement_context_stopped_wp store (rootWidth v4) addr cidr hw ha hc
    (rootSlot v4) (c.append (gapContext parent side sibling)) n l r
    (by simpa only [Context.plug_append, gapContext_plug] using hr)
    (by simpa only [Context.plug_append, gapContext_plug] using hv) hpctx hstop
  have hlast : (gapContext parent side sibling).lastParent (c.lastParent none) = some parent.id := by
    unfold gapContext
    split <;> rfl
  simp only [Context.plug_append, gapContext_plug, Context.lastParent_append, hlast] at nativePlacement
  obtain ⟨trie, htrie⟩ : ∃ trie, (c.plug (Tree.fork parent side (.node n l r) sibling)).root = some trie := by
    cases c with
    | here => exact ⟨parent.id, Tree.fork_root parent side (.node n l r) sibling⟩
    | left a inner r => exact ⟨a.id, rfl⟩
    | right a l inner => exact ⟨a.id, rfl⟩
  rw [htrie] at nativePlacement
  have hplacement : ⦃fun w => ⌜w = k⌝⦄
      (MonadLift.monadLift (WG.nodePlacement (some trie) addr cidr (rootWidth v4)) : WG.M (Option Nat × Bool))
      ⦃⇓ result w => ⌜result = (some parent.id, false) ∧ w = k⌝⦄ := by
    apply (total_iff_run_ambient _ _ _).mpr
    intro w ambient hw
    subst w
    obtain ⟨x, st, ambient', hrun, hx, hs⟩ :=
      (total_iff_run_ambient _ _ _).mp nativePlacement store ambient rfl
    subst st
    refine ⟨x, k, ambient', ?_, hx, rfl⟩
    change ((WG.liftAip _).run k).run ambient = _
    rw [liftAip_run, hd]
    simp only [store] at hrun
    simp only [hrun, Except.map]
    change Except.ok ((x, {k with dev := some d}), ambient') = _
    rw [← hd]
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
