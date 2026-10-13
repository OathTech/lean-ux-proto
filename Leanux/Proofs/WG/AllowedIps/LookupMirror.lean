import Leanux.Proofs.WG.AllowedIps.Store
import Leanux.Proofs.WG.AllowedIps.ArithmeticMirror
import Leanux.Proofs.WG.Keypairs.Frames.WGBase

/-!
# Original allowed-IP lookup over represented stores

The loop invariant retains the current subtree, the best earlier match, and
a height budget for the remaining range iterations. The proof uses the
original mirror action, including its early returns and explicit error.
Mutation preservation and configuration history are separate obligations.

The WGBase import reuses the canonical generated match declarations for
`findNode` already present in the proof tree.
-/

set_option pp.structureInstances false

namespace Leanux.Proofs.WG.AllowedIps

open Leanux Std.Do Leanux.Proofs.Framing

theorem getNode_wp (k : Kernel) (d : WG.Device) (id : Nat) (n : WG.AipNode)
    (hd : k.wg = some d) (hn : d.nodes[id]? = some n) :
    ⦃fun w => ⌜w.k = k⌝⦄ WG.getNode id ⦃⇓ x w => ⌜x = n ∧ w.k = k⌝⦄ := by
  apply (total_iff_run _ _ _).mpr
  intro w hk
  exact ⟨n, w, getNode_run w d id n (hk ▸ hd) hn, rfl, hk⟩

theorem prefixMatches_wp (k : Kernel) (n : WG.AipNode) (key width : Nat)
    (hw : width = 32 ∨ width = 128) (hn : n.bits < 2 ^ width)
    (hk : key < 2 ^ width) (hc : n.cidr ≤ width) :
    ⦃fun w => ⌜w.k = k⌝⦄ WG.prefixMatches n key width
    ⦃⇓ x w => ⌜x = decide (prefixBits width n.cidr n.bits =
      prefixBits width n.cidr key) ∧ w.k = k⌝⦄ := by
  apply (total_iff_run _ _ _).mpr
  intro w h
  exact ⟨_, _, prefixMatches_run n key width w hw hn hk hc,
    rfl, (commonRecords_k ..).trans h⟩

theorem choose_wp (k : Kernel) (n : WG.AipNode) (key : Nat)
    (hc : n.cidr < n.bitlen) :
    ⦃fun w => ⌜w.k = k⌝⦄ WG.choose n key
    ⦃⇓ x w => ⌜x = bit n.bitlen n.cidr key ∧ w.k = k⌝⦄ := by
  apply (total_iff_run _ _ _).mpr
  intro w h
  exact ⟨_, w, choose_run n key w hc, rfl, h⟩

theorem bitAt_wp (k : Kernel) (width : Nat) (parent : WG.Slot) (n : NodeData)
    (l r : Tree) (b : Nat) (hb : b < 2) :
    ⦃fun w => ⌜w.k = k⌝⦄ (encode width parent n l r).bitAt b
    ⦃⇓ x w => ⌜x = (Tree.child l r b).root ∧ w.k = k⌝⦄ := by
  apply (total_iff_run _ _ _).mpr
  intro w h
  exact ⟨_, w, encode_bitAt_run width parent n l r b w hb, rfl, h⟩

/-- The answer still lies in the current subtree, unless the previous best
match is the winner. There is one iteration reserved for an empty cursor. -/
def SearchState (k : Kernel) (d : WG.Device) (width key : Nat) (answer : Option Nat)
    (remaining : Nat) (node found : Option Nat) (w : World) : Prop :=
  w.k = k ∧ ∃ parent t, RepAt d.nodes width parent t ∧ t.Valid width ∧
    node = t.root ∧ answer = (t.lookupId width key).or found ∧ t.height + 1 ≤ remaining

/-- Total correctness of the original 130-iteration traversal under a
structurally represented valid tree. Errors have the false postcondition. -/
theorem findNode_wp (k : Kernel) (d : WG.Device) (width key : Nat)
    (hw : width = 32 ∨ width = 128) (hk : key < 2 ^ width)
    (hd : k.wg = some d) (t : Tree) (parent : WG.Slot)
    (hr : RepAt d.nodes width parent t) (hv : t.Valid width) :
    ⦃fun w => ⌜w.k = k⌝⦄ WG.findNode t.root width key
    ⦃⇓ x w => ⌜x = t.lookupId width key ∧ w.k = k⌝⦄ := by
  mvcgen [WG.findNode, branch, invariant]
  invariants
  | inv1 => Invariant.withEarlyReturnNewDo
      (fun cursor state w => ⌜SearchState k d width key (t.lookupId width key)
        cursor.suffix.length state.1 state.2 w⌝)
      (fun result _ w => ⌜result = t.lookupId width key ∧ w.k = k⌝)
      ExceptConds.false
  case vc1.step.h_1 =>
    dsimp +zetaDelta only at *
    rename_i _ _ _ _ _ hnone w hi _
    try simp only [List.cons_ne_nil, and_false, false_and, exists_false, or_false] at hi
    rcases hi.2 with ⟨hkw, p, u, hrep, hvalid, hroot, hans, hbudget⟩
    cases u with
    | empty => simp_all [Tree.root]
    | node n l r => simp [Tree.root] at hroot; grind
  case vc2.step.h_2 =>
    dsimp +zetaDelta only at *
    rename_i _ _ _ _ _ id hsome w hi _
    try simp only [List.cons_ne_nil, and_false, false_and, exists_false, or_false] at hi
    rcases hi.2 with ⟨hkw, p, u, hrep, hvalid, hroot, hans, hbudget⟩
    cases u with
    | empty => simp [Tree.root] at hroot; grind
    | node n l r =>
      have hid : id = n.id := by simpa [Tree.root, hsome] using hroot
      subst id
      have getter := getNode_wp k d n.id (encode width p n l r) hd hrep.1
      have matching := prefixMatches_wp k (encode width p n l r) key width hw
        hvalid.1 hk hvalid.2.1
      mvcgen [getter]
      rename_i fetched current hfetched
      rcases hfetched with ⟨rfl, hcurrent⟩
      mvcgen [matching]
      all_goals try dsimp +zetaDelta only at *
      all_goals try simp_all [encode, Tree.lookupId_node, Tree.root]
      all_goals try mvcgen [WG.choose, WG.AipNode.bitAt, invariant]
      all_goals try dsimp +zetaDelta only at *
      all_goals try simp_all
      all_goals try (have bound := hvalid.2.1; omega)
      all_goals try (have bound := Nat.mod_lt (key / 2 ^ (width - 1 - n.cidr)) (by decide : 0 < 2); omega)
      all_goals
        first
        | have hm := of_decide_eq_false (p := prefixBits width n.cidr n.addr =
              prefixBits width n.cidr key) (by assumption)
          simp_all
        | have hm := of_decide_eq_true (p := prefixBits width n.cidr n.addr =
              prefixBits width n.cidr key) (by assumption)
          simp_all
          refine ⟨rfl, .child n.id (bit width n.cidr key),
            Tree.child l r (bit width n.cidr key),
            hrep.child (bit_lt_two ..), hvalid.child _, ?_, ?_, ?_⟩
          · have cases : bit width n.cidr key = 0 ∨ bit width n.cidr key = 1 := by
              have bound := bit_lt_two width n.cidr key
              omega
            rcases cases with hb | hb <;> simp_all [Tree.child, bit, Tree.root]
          · simp_all
          · have decrease := Tree.child_height_lt n l r (bit width n.cidr key)
            try simp only [List.length_cons] at hbudget
            omega
  case vc3.pre =>
    dsimp +zetaDelta only at *
    rename_i w hkw
    refine Or.inl ⟨trivial, hkw, parent, t, hr, hv, rfl, by simp, ?_⟩
    change t.height + 1 ≤ 130
    have height := Tree.height_le hv
    rcases hw with rfl | rfl <;> omega
  case vc4.post.success.h_1 =>
    dsimp +zetaDelta only at *
    grind
  case vc5.post.success.h_2 =>
    dsimp +zetaDelta only at *
    simp_all [SearchState]

/-- The original traversal always returns normally on a represented valid
tree of either supported family, with the pure answer and unchanged Kernel. -/
theorem findNode_run (w : World) (d : WG.Device) (width key : Nat)
    (hw : width = 32 ∨ width = 128) (hk : key < 2 ^ width)
    (hd : w.k.wg = some d) (t : Tree) (parent : WG.Slot)
    (hr : RepAt d.nodes width parent t) (hv : t.Valid width) :
    ∃ w', (WG.findNode t.root width key).run w = .ok (t.lookupId width key, w') ∧
      w'.k = w.k := by
  obtain ⟨x, w', he, hx, hframe⟩ := (total_iff_run _ _ _).mp
    (findNode_wp w.k d width key hw hk hd t parent hr hv) w rfl
  exact ⟨w', hx ▸ he, hframe⟩

/-- Successful executions of the unchanged mirror traversal return exactly
the node identifier selected by the represented pure tree. The whole Kernel
is preserved; branch records remain in the returned World. -/
theorem findNode_refines (w w' : World) (d : WG.Device) (width key : Nat)
    (hw : width = 32 ∨ width = 128) (hk : key < 2 ^ width)
    (hd : w.k.wg = some d) (t : Tree) (parent : WG.Slot)
    (hr : RepAt d.nodes width parent t) (hv : t.Valid width) (result : Option Nat)
    (hreturn : (WG.findNode t.root width key).run w = .ok (result, w')) :
    result = t.lookupId width key ∧ w'.k = w.k := by
  obtain ⟨v, hex, hframe⟩ := findNode_run w d width key hw hk hd t parent hr hv
  rw [hreturn] at hex
  cases hex
  exact ⟨rfl, hframe⟩

end Leanux.Proofs.WG.AllowedIps
