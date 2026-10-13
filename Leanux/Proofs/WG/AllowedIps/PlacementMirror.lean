import Leanux.Proofs.WG.AllowedIps.Context
import Leanux.Proofs.WG.AllowedIps.LookupMirror

/-! Total refinement of original node placement. The witness is a tree
context with local path conditions, not a second executable traversal. -/
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.AllowedIps
open Leanux Std.Do Leanux.Proofs.Framing

def PlacementState (k : Kernel) (d : WG.Device) (width key cidr : Nat)
    (base : WG.Slot) (whole : Tree) (remaining : Nat)
    (node parent : Option Nat) (w : World) : Prop :=
  w.k = k ∧ ∃ (c : Context) (u : Tree), whole = c.plug u ∧ c.Follows width key cidr ∧
    RepAt d.nodes width (c.slot base) u ∧ u.Valid width ∧
    node = u.root ∧ parent = c.lastParent none ∧ u.height + 1 ≤ remaining

theorem nodePlacement_wp (k : Kernel) (d : WG.Device) (width key cidr : Nat)
    (hw : width = 32 ∨ width = 128) (hk : key < 2 ^ width) (hc : cidr ≤ width)
    (hd : k.wg = some d) (t : Tree) (base : WG.Slot)
    (hr : RepAt d.nodes width base t) (hv : t.Valid width) :
    ⦃fun w => ⌜w.k = k⌝⦄ WG.nodePlacement t.root key cidr width
    ⦃⇓ result w => ⌜w.k = k ∧ PlacementWitness t width key cidr result⌝⦄ := by
  mvcgen [WG.nodePlacement, branch, branchCmp, invariant]
  invariants
  | inv1 => Invariant.withEarlyReturnNewDo
      (fun cursor state w => ⌜PlacementState k d width key cidr base t
        cursor.suffix.length state.1 state.2 w⌝)
      (fun result _ w => ⌜w.k = k ∧ PlacementWitness t width key cidr result⌝)
      ExceptConds.false
  case vc1.step.h_1 =>
    dsimp +zetaDelta only at *
    rename_i _ _ _ _ _ hnone w hi _
    try simp only [List.cons_ne_nil, and_false, false_and, exists_false, or_false] at hi
    rcases hi.2 with ⟨hkw, c, u, hplug, hfollow, hrep, hvalid, hroot, hparent, hbudget⟩
    cases u with
    | empty =>
      refine .inr ⟨_, rfl, trivial, hkw, c, .empty, hplug, hfollow, ?_⟩
      simp_all [PlacementEnd]
    | node n l r => simp [Tree.root] at hroot; grind
  case vc2.step.h_2 =>
    dsimp +zetaDelta only at *
    rename_i _ _ _ _ _ id hsome w hi _
    try simp only [List.cons_ne_nil, and_false, false_and, exists_false, or_false] at hi
    rcases hi.2 with ⟨hkw, c, u, hplug, hfollow, hrep, hvalid, hroot, hparent, hbudget⟩
    cases u with
    | empty => simp [Tree.root] at hroot; grind
    | node n l r =>
      have hid : id = n.id := by simpa [Tree.root, hsome] using hroot
      subst id
      have getter := getNode_wp k d n.id (encode width (c.slot base) n l r) hd hrep.1
      have matching := prefixMatches_wp k (encode width (c.slot base) n l r) key width hw
        hvalid.1 hk hvalid.2.1
      mvcgen [getter]
      all_goals try dsimp +zetaDelta only at *
      all_goals try simp_all [encode]
      all_goals try mvcgen [matching]
      all_goals try dsimp +zetaDelta only at *
      all_goals try simp_all [encode]
      all_goals try exact ⟨c, .node n l r, rfl, hfollow, .inl ⟨by assumption, rfl⟩⟩
      all_goals try exact ⟨c, .node n l r, rfl, hfollow,
        .inr (.inl ⟨by assumption, of_decide_eq_false (by assumption), rfl⟩)⟩
      all_goals try exact ⟨c, .node n l r, rfl, hfollow,
        .inr (.inr ⟨by assumption, by
          rw [show n.cidr = cidr from by assumption]
          assumption, rfl⟩)⟩
      have hlt : n.cidr < cidr := by omega
      have hm : prefixBits width n.cidr n.addr = prefixBits width n.cidr key := by
        exact of_decide_eq_true (by assumption)
      mvcgen [WG.choose, WG.AipNode.bitAt, invariant]
      all_goals try dsimp +zetaDelta only at *
      all_goals try simp_all [encode]
      all_goals try omega
      refine ⟨rfl, c.append (Context.edge n l r (bit width n.cidr key)),
        Tree.child l r (bit width n.cidr key), by simp,
        hfollow.append (Context.edge_follows n l r hlt hm), ?_, hvalid.child _, ?_, ?_, ?_⟩
      · simpa only [Context.slot_append, Context.edge_slot n l r (bit_lt_two ..)] using
          hrep.child (bit_lt_two width n.cidr key)
      · have cases : bit width n.cidr key = 0 ∨ bit width n.cidr key = 1 := by
          have bound := bit_lt_two width n.cidr key
          omega
        rcases cases with hb | hb <;> simp_all [Tree.child, bit]
      · simp [Tree.root]
      · have decrease := Tree.child_height_lt n l r (bit width n.cidr key)
        try simp only [List.length_cons] at hbudget
        omega
  case vc3.pre =>
    dsimp +zetaDelta only at *
    rename_i w hkw
    refine Or.inl ⟨trivial, hkw, .here, t, rfl, trivial, hr, hv, rfl, rfl, ?_⟩
    change t.height + 1 ≤ 130
    have height := Tree.height_le hv
    rcases hw with rfl | rfl <;> omega
  case vc4.post.success.h_1 =>
    dsimp +zetaDelta only at *
    grind
  case vc5.post.success.h_2 =>
    dsimp +zetaDelta only at *
    simp_all [PlacementState]

/-- Normal completion of the original traversal, with structural placement
evidence and the complete Kernel unchanged. -/
theorem nodePlacement_run (w : World) (d : WG.Device) (width key cidr : Nat)
    (hw : width = 32 ∨ width = 128) (hk : key < 2 ^ width) (hc : cidr ≤ width)
    (hd : w.k.wg = some d) (t : Tree) (base : WG.Slot)
    (hr : RepAt d.nodes width base t) (hv : t.Valid width) :
    ∃ result w', (WG.nodePlacement t.root key cidr width).run w = .ok (result, w') ∧
      w'.k = w.k ∧ PlacementWitness t width key cidr result :=
  (total_iff_run _ _ _).mp (nodePlacement_wp w.k d width key cidr hw hk hc hd t base hr hv) w rfl

theorem nodePlacement_refines (w w' : World) (d : WG.Device) (width key cidr : Nat)
    (hw : width = 32 ∨ width = 128) (hk : key < 2 ^ width) (hc : cidr ≤ width)
    (hd : w.k.wg = some d) (t : Tree) (base : WG.Slot)
    (hr : RepAt d.nodes width base t) (hv : t.Valid width) (result : Option Nat × Bool)
    (hreturn : (WG.nodePlacement t.root key cidr width).run w = .ok (result, w')) :
    w'.k = w.k ∧ PlacementWitness t width key cidr result := by
  obtain ⟨r, v, he, hf⟩ := nodePlacement_run w d width key cidr hw hk hc hd t base hr hv
  rw [hreturn] at he
  cases he
  exact hf

/-- A known empty focus reached by the request determines the exact parent
returned by the original traversal. The complete Kernel stays unchanged. -/
theorem nodePlacement_empty_focus_wp (k : Kernel) (d : WG.Device) (width key cidr : Nat)
    (hw : width = 32 ∨ width = 128) (hk : key < 2 ^ width) (hc : cidr ≤ width)
    (hd : k.wg = some d) (c : Context) (base : WG.Slot)
    (hr : RepAt d.nodes width base (c.plug .empty))
    (hv : (c.plug .empty).Valid width) (hf : c.Follows width key cidr) :
    ⦃fun w => ⌜w.k = k⌝⦄ WG.nodePlacement (c.plug .empty).root key cidr width
    ⦃⇓ result w => ⌜result = (c.lastParent none, false) ∧ w.k = k⌝⦄ := by
  apply (total_iff_run _ _ _).mpr
  intro w hkw
  obtain ⟨result, v, he, hframe, hp⟩ := nodePlacement_run w d width key cidr hw hk hc
    (hkw ▸ hd) (c.plug .empty) base hr hv
  exact ⟨result, v, he, hp.empty_result hf, hframe.trans hkw⟩

end Leanux.Proofs.WG.AllowedIps
