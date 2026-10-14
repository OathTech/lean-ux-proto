import Leanux.Proofs.WG.AllowedIps.RemovalCollapse

/-! Total original steps, including list deletion before the target read.
Collapse premises describe resident input snapshots and distinct slots;
all intermediate parent and sibling reads are derived from those inputs. -/
set_option maxHeartbeats 1000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Std.Do Leanux.Proofs.Framing

def removalCollapseRoot (d : WG.Device) (id : Nat) (n : WG.AipNode)
    (parent side : Nat) (pn : WG.AipNode) (v4 : Bool)
    (sibling : Option (Nat × WG.AipNode)) : WG.Device :=
  removalParentRoot (removalLeafDetached d id n parent side pn) parent v4 sibling

def removalCollapseChild (d : WG.Device) (id : Nat) (n : WG.AipNode)
    (parent side : Nat) (pn : WG.AipNode) (grand gside : Nat) (gn : WG.AipNode)
    (sibling : Option (Nat × WG.AipNode)) : WG.Device :=
  removalParentChild (removalLeafDetached d id n parent side pn) parent grand gside gn sibling

theorem removalLeafDetached_parent (d : WG.Device) (id : Nat) (n : WG.AipNode)
    (parent side : Nat) (pn : WG.AipNode) (hip : id ≠ parent) :
    (removalLeafDetached d id n parent side pn).nodes[parent]? =
      some { pn with bit := pn.bit.set! side none } := by
  simp [removalLeafDetached, Std.TreeMap.getElem?_erase, hip]

theorem removalLeafDetached_other (d : WG.Device) (id : Nat) (n : WG.AipNode)
    (parent side : Nat) (pn : WG.AipNode) (q : Nat) (hi : id ≠ q) (hp : parent ≠ q) :
    (removalLeafDetached d id n parent side pn).nodes[q]? = d.nodes[q]? := by
  simp [removalLeafDetached, removalCleared, Std.TreeMap.getElem?_erase,
    Std.TreeMap.getElem?_insert, hi, hp]

theorem removeNodeBody_leaf_collapse_root_wp (k : Kernel) (d : WG.Device)
    (hd : k.wg = some d) (id parent side : Nat) (n pn : WG.AipNode)
    (hn : d.nodes[id]? = some n) (hp : d.nodes[parent]? = some pn)
    (hip : id ≠ parent) (hb : side ≤ 1) (howner : pn.peer = none)
    (hbits : n.bit = #[none, none]) (hparent : n.parent = .child parent side)
    (v4 : Bool) (hbase : pn.parent = rootSlot v4) (sibling : Option (Nat × WG.AipNode))
    (hbit : pn.bit[1-side]? = some (sibling.map Prod.fst))
    (hs : ∀ c cn, sibling = some (c, cn) → d.nodes[c]? = some cn ∧ c ≠ id ∧ c ≠ parent) :
    ⦃fun w => ⌜w.k = k⌝⦄ removeNodeBody id
    ⦃⇓ result w => ⌜result = .yield () ∧ w.k = { k with wg := some (removalCollapseRoot d id n parent side pn v4 sibling) }⌝⦄ := by
  let dp := removalLeafDetached d id n parent side pn
  have hpp := removalLeafDetached_parent d id n parent side pn hip
  have hsp : ∀ c cn, sibling = some (c, cn) → dp.nodes[c]? = some cn ∧ c ≠ parent := by
    intro c cn he
    obtain ⟨hc, hci, hcp⟩ := hs c cn he
    exact ⟨(removalLeafDetached_other d id n parent side pn c (Ne.symm hci) (Ne.symm hcp)).trans hc, hcp⟩
  have ht := removeParentTail_root_wp { k with wg := some dp } dp rfl parent
    { pn with bit := pn.bit.set! side none } v4 sibling hpp hbase hsp
  apply (total_iff_run _ _ _).mpr
  intro w hkw
  let start := { removalRecords w removalCollapseRecords with k := { k with wg := some dp } }
  obtain ⟨result, w', he, hx, hk⟩ := (total_iff_run _ _ _).mp ht start rfl
  refine ⟨result, w', ?_, hx, ?_⟩
  · rw [removeNodeBody_leaf_collapse_run w d (hkw ▸ hd) id parent side n pn hn hp hip hb
      howner hbits hparent (sibling.map Prod.fst) hbit]
    simpa only [hkw] using he
  · exact hk

theorem removeNodeBody_leaf_collapse_child_wp (k : Kernel) (d : WG.Device)
    (hd : k.wg = some d) (id parent side grand gside : Nat) (n pn gn : WG.AipNode)
    (hn : d.nodes[id]? = some n) (hp : d.nodes[parent]? = some pn)
    (hg : d.nodes[grand]? = some gn) (hip : id ≠ parent) (hig : id ≠ grand)
    (hpg : parent ≠ grand) (hb : side ≤ 1) (hgb : gside ≤ 1) (howner : pn.peer = none)
    (hbits : n.bit = #[none, none]) (hparent : n.parent = .child parent side)
    (hbase : pn.parent = .child grand gside) (sibling : Option (Nat × WG.AipNode))
    (hbit : pn.bit[1-side]? = some (sibling.map Prod.fst))
    (hs : ∀ c cn, sibling = some (c, cn) →
      d.nodes[c]? = some cn ∧ c ≠ id ∧ c ≠ parent ∧ c ≠ grand) :
    ⦃fun w => ⌜w.k = k⌝⦄ removeNodeBody id
    ⦃⇓ result w => ⌜result = .yield () ∧ w.k = { k with wg := some (removalCollapseChild d id n parent side pn grand gside gn sibling) }⌝⦄ := by
  let dp := removalLeafDetached d id n parent side pn
  have hpp := removalLeafDetached_parent d id n parent side pn hip
  have hgp : dp.nodes[grand]? = some gn :=
    (removalLeafDetached_other d id n parent side pn grand hig hpg).trans hg
  have hsp : ∀ c cn, sibling = some (c, cn) →
      dp.nodes[c]? = some cn ∧ c ≠ parent ∧ c ≠ grand := by
    intro c cn he
    obtain ⟨hc, hci, hcp, hcg⟩ := hs c cn he
    exact ⟨(removalLeafDetached_other d id n parent side pn c (Ne.symm hci) (Ne.symm hcp)).trans hc,
      hcp, hcg⟩
  have ht := removeParentTail_child_wp { k with wg := some dp } dp rfl parent grand gside
    { pn with bit := pn.bit.set! side none } gn sibling hpp hgp hbase hpg hgb hsp
  apply (total_iff_run _ _ _).mpr
  intro w hkw
  let start := { removalRecords w removalCollapseRecords with k := { k with wg := some dp } }
  obtain ⟨result, w', he, hx, hk⟩ := (total_iff_run _ _ _).mp ht start rfl
  refine ⟨result, w', ?_, hx, ?_⟩
  · rw [removeNodeBody_leaf_collapse_run w d (hkw ▸ hd) id parent side n pn hn hp hip hb
      howner hbits hparent (sibling.map Prod.fst) hbit]
    simpa only [hkw] using he
  · exact hk

theorem removeStep_child_unary_wp (k : Kernel) (d : WG.Device) (hd : k.wg = some d)
    (left : Bool) (id parent side child : Nat) (n pn cn : WG.AipNode)
    (hn : d.nodes[id]? = some n) (hp : d.nodes[parent]? = some pn)
    (hc : d.nodes[child]? = some cn) (hip : id ≠ parent) (hic : id ≠ child)
    (hcp : child ≠ parent) (hb : side ≤ 1)
    (hbits : n.bit = if left then #[some child, none] else #[none, some child])
    (hparent : n.parent = .child parent side) :
    ⦃fun w => ⌜w.k = k⌝⦄ removeStep id
    ⦃⇓ result w => ⌜result = .yield () ∧ w.k = { k with wg := some (removalChildUnary (unlisted d id) id n parent side pn child cn) }⌝⦄ := by
  have hl := listDel_wp k d hd id
  have hn := removeNodeBody_child_unary_wp { k with wg := some (unlisted d id) }
    (unlisted d id) rfl left id parent side child n pn cn hn hp hc hip hic hcp hb hbits hparent
  mvcgen [removeStep, branch, hl, hn]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

theorem removeStep_child_leaf_owned_wp (k : Kernel) (d : WG.Device)
    (hd : k.wg = some d) (id parent side : Nat) (n pn : WG.AipNode)
    (hn : d.nodes[id]? = some n) (hp : d.nodes[parent]? = some pn)
    (hip : id ≠ parent) (hb : side ≤ 1) (howner : pn.peer.isSome)
    (hbits : n.bit = #[none, none]) (hparent : n.parent = .child parent side) :
    ⦃fun w => ⌜w.k = k⌝⦄ removeStep id
    ⦃⇓ result w => ⌜result = .yield () ∧ w.k = { k with wg := some (removalLeafDetached (unlisted d id) id n parent side pn) }⌝⦄ := by
  have hl := listDel_wp k d hd id
  have hn := removeNodeBody_child_leaf_owned_wp { k with wg := some (unlisted d id) }
    (unlisted d id) rfl id parent side n pn hn hp hip hb howner hbits hparent
  mvcgen [removeStep, branch, hl, hn]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

theorem removeStep_leaf_collapse_root_wp (k : Kernel) (d : WG.Device)
    (hd : k.wg = some d) (id parent side : Nat) (n pn : WG.AipNode)
    (hn : d.nodes[id]? = some n) (hp : d.nodes[parent]? = some pn)
    (hip : id ≠ parent) (hb : side ≤ 1) (howner : pn.peer = none)
    (hbits : n.bit = #[none, none]) (hparent : n.parent = .child parent side)
    (v4 : Bool) (hbase : pn.parent = rootSlot v4) (sibling : Option (Nat × WG.AipNode))
    (hbit : pn.bit[1-side]? = some (sibling.map Prod.fst))
    (hs : ∀ c cn, sibling = some (c, cn) → d.nodes[c]? = some cn ∧ c ≠ id ∧ c ≠ parent) :
    ⦃fun w => ⌜w.k = k⌝⦄ removeStep id
    ⦃⇓ result w => ⌜result = .yield () ∧ w.k = { k with wg := some (removalCollapseRoot (unlisted d id) id n parent side pn v4 sibling) }⌝⦄ := by
  have hl := listDel_wp k d hd id
  have hn := removeNodeBody_leaf_collapse_root_wp { k with wg := some (unlisted d id) }
    (unlisted d id) rfl id parent side n pn hn hp hip hb howner hbits hparent v4 hbase sibling hbit hs
  mvcgen [removeStep, branch, hl, hn]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

theorem removeStep_leaf_collapse_child_wp (k : Kernel) (d : WG.Device)
    (hd : k.wg = some d) (id parent side grand gside : Nat) (n pn gn : WG.AipNode)
    (hn : d.nodes[id]? = some n) (hp : d.nodes[parent]? = some pn)
    (hg : d.nodes[grand]? = some gn) (hip : id ≠ parent) (hig : id ≠ grand)
    (hpg : parent ≠ grand) (hb : side ≤ 1) (hgb : gside ≤ 1) (howner : pn.peer = none)
    (hbits : n.bit = #[none, none]) (hparent : n.parent = .child parent side)
    (hbase : pn.parent = .child grand gside) (sibling : Option (Nat × WG.AipNode))
    (hbit : pn.bit[1-side]? = some (sibling.map Prod.fst))
    (hs : ∀ c cn, sibling = some (c, cn) →
      d.nodes[c]? = some cn ∧ c ≠ id ∧ c ≠ parent ∧ c ≠ grand) :
    ⦃fun w => ⌜w.k = k⌝⦄ removeStep id
    ⦃⇓ result w => ⌜result = .yield () ∧ w.k = { k with wg := some (removalCollapseChild (unlisted d id) id n parent side pn grand gside gn sibling) }⌝⦄ := by
  have hl := listDel_wp k d hd id
  have hn := removeNodeBody_leaf_collapse_child_wp { k with wg := some (unlisted d id) }
    (unlisted d id) rfl id parent side grand gside n pn gn hn hp hg hip hig hpg hb hgb
    howner hbits hparent hbase sibling hbit hs
  mvcgen [removeStep, branch, hl, hn]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

end Leanux.Proofs.WG.AllowedIps
