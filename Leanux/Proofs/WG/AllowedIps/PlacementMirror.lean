import Leanux.Proofs.WG.AllowedIps.Context
import Leanux.Proofs.WG.AllowedIps.LookupMirror

/-! Total refinement of original node placement. The witness is a tree
context with local path conditions, not a second executable traversal. -/
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.AllowedIps
open Leanux Std.Do Leanux.Proofs.Framing

def PlacementState (k : WG.AipStore) (width key cidr : Nat)
    (base : WG.Slot) (whole : Tree) (remaining : Nat)
    (node parent : Option Nat) (w : WG.AipStore) : Prop :=
  w = k ∧ ∃ (c : Context) (u : Tree), whole = c.plug u ∧ c.Follows width key cidr ∧
    RepAt k.nodes width (c.slot base) u ∧ u.Valid width ∧
    node = u.root ∧ parent = c.lastParent none ∧ u.height + 1 ≤ remaining

theorem nodePlacement_wp (k : WG.AipStore) (width key cidr : Nat)
    (hw : width = 32 ∨ width = 128) (hk : key < 2 ^ width) (hc : cidr ≤ width)
    (t : Tree) (base : WG.Slot)
    (hr : RepAt k.nodes width base t) (hv : t.Valid width) :
    ⦃fun w => ⌜w = k⌝⦄ WG.nodePlacement t.root key cidr width
    ⦃⇓ result w => ⌜w = k ∧ PlacementWitness t width key cidr result⌝⦄ := by
  mvcgen [WG.nodePlacement, branch, AmbientM.branch, branchCmp, AmbientM.branchCmp, invariant, AmbientM.invariant]
  invariants
  | inv1 => Invariant.withEarlyReturnNewDo
      (fun cursor state w => ⌜PlacementState k width key cidr base t
        cursor.suffix.length state.1 state.2 w⌝)
      (fun result _ w => ⌜w = k ∧ PlacementWitness t width key cidr result⌝)
      ExceptConds.false
  case vc1.step.h_1 =>
    dsimp +zetaDelta only at *
    rename_i _ _ _ _ _ hnone w ambient hi _
    try simp only [List.cons_ne_nil, and_false, false_and, exists_false, or_false] at hi
    rcases hi.2 with ⟨hkw, c, u, hplug, hfollow, hrep, hvalid, hroot, hparent, hbudget⟩
    cases u with
    | empty =>
      refine .inr ⟨_, rfl, trivial, hkw, c, .empty, hplug, hfollow, ?_⟩
      simp_all [PlacementEnd]
    | node n l r => simp [Tree.root] at hroot; grind
  case vc2.step.h_2 =>
    dsimp +zetaDelta only at *
    rename_i _ _ _ _ _ id hsome w ambient hi _
    try simp only [List.cons_ne_nil, and_false, false_and, exists_false, or_false] at hi
    rcases hi.2 with ⟨hkw, c, u, hplug, hfollow, hrep, hvalid, hroot, hparent, hbudget⟩
    cases u with
    | empty => simp [Tree.root] at hroot; grind
    | node n l r =>
      have hid : id = n.id := by simpa [Tree.root, hsome] using hroot
      subst id
      have getter := getNode_wp k n.id (encode width (c.slot base) n l r) hrep.1
      have matching := prefixMatches_wp k (encode width (c.slot base) n l r) key width hw
        hvalid.1 hk hvalid.2.1
      mvcgen [getter]
      all_goals try dsimp +zetaDelta only at *
      all_goals try simp_all [encode]
      all_goals try mvcgen [matching]
      all_goals try dsimp +zetaDelta only at *
      all_goals try simp_all []
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
      mvcgen [WG.choose, WG.AipNode.bitAt, invariant, AmbientM.invariant]
      all_goals try dsimp +zetaDelta only at *
      all_goals try simp_all []
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
    rename_i w ambient hkw
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
evidence and the complete native AipStore unchanged. -/
theorem nodePlacement_run (w : WG.AipStore) (ambient : Ambient) (width key cidr : Nat)
    (hw : width = 32 ∨ width = 128) (hk : key < 2 ^ width) (hc : cidr ≤ width)
    (t : Tree) (base : WG.Slot)
    (hr : RepAt w.nodes width base t) (hv : t.Valid width) :
    ∃ result w' ambient', ((WG.nodePlacement t.root key cidr width).run w).run ambient =
      .ok ((result, w'), ambient') ∧ w' = w ∧ PlacementWitness t width key cidr result :=
  (total_iff_run_ambient _ _ _).mp
    (nodePlacement_wp w width key cidr hw hk hc t base hr hv) w ambient rfl

theorem nodePlacement_refines (w w' : WG.AipStore) (ambient ambient' : Ambient)
    (width key cidr : Nat) (hw : width = 32 ∨ width = 128)
    (hk : key < 2 ^ width) (hc : cidr ≤ width)
    (t : Tree) (base : WG.Slot)
    (hr : RepAt w.nodes width base t) (hv : t.Valid width) (result : Option Nat × Bool)
    (hreturn : ((WG.nodePlacement t.root key cidr width).run w).run ambient =
      .ok ((result, w'), ambient')) :
    w' = w ∧ PlacementWitness t width key cidr result := by
  obtain ⟨r, v, finalAmbient, he, hf⟩ := nodePlacement_run w ambient width key cidr hw hk hc t base hr hv
  rw [hreturn] at he
  cases he
  exact hf

/-- A known empty focus reached by the request determines the exact parent
returned by the original traversal. The complete native store stays unchanged. -/
theorem nodePlacement_empty_focus_wp (k : WG.AipStore) (width key cidr : Nat)
    (hw : width = 32 ∨ width = 128) (hk : key < 2 ^ width) (hc : cidr ≤ width)
    (c : Context) (base : WG.Slot)
    (hr : RepAt k.nodes width base (c.plug .empty))
    (hv : (c.plug .empty).Valid width) (hf : c.Follows width key cidr) :
    ⦃fun w => ⌜w = k⌝⦄ WG.nodePlacement (c.plug .empty).root key cidr width
    ⦃⇓ result w => ⌜result = (c.lastParent none, false) ∧ w = k⌝⦄ := by
  apply (total_iff_run_ambient _ _ _).mpr
  intro w ambient hkw
  obtain ⟨result, v, finalAmbient, he, hframe, hp⟩ :=
    nodePlacement_run w ambient width key cidr hw hk hc (c.plug .empty) base (hkw ▸ hr) hv
  exact ⟨result, v, finalAmbient, he, hp.empty_result hf, hframe.trans hkw⟩

theorem nodePlacement_exact_focus_wp (k : WG.AipStore) (width key cidr : Nat)
    (hw : width = 32 ∨ width = 128) (hk : key < 2 ^ width) (hc : cidr ≤ width)
    (c : Context) (base : WG.Slot) (n : NodeData) (l r : Tree)
    (hr : RepAt k.nodes width base (c.plug (.node n l r)))
    (hv : (c.plug (.node n l r)).Valid width) (hf : c.Follows width key cidr)
    (hn : n.cidr = cidr) (hm : prefixBits width n.cidr n.addr = prefixBits width n.cidr key) :
    ⦃fun w => ⌜w = k⌝⦄ WG.nodePlacement (c.plug (.node n l r)).root key cidr width
    ⦃⇓ result w => ⌜result = (some n.id, true) ∧ w = k⌝⦄ := by
  apply (total_iff_run_ambient _ _ _).mpr
  intro w ambient hkw
  obtain ⟨result, v, finalAmbient, he, hframe, hp⟩ :=
    nodePlacement_run w ambient width key cidr hw hk hc (c.plug (.node n l r)) base (hkw ▸ hr) hv
  exact ⟨result, v, finalAmbient, he, hp.exact_result hf hn hm, hframe.trans hkw⟩

end Leanux.Proofs.WG.AllowedIps
