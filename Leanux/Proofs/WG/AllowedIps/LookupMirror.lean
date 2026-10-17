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

theorem getNode_wp (k : WG.AipStore) (id : Nat) (n : WG.AipNode)
    (hn : k.nodes[id]? = some n) :
    ⦃fun w => ⌜w = k⌝⦄ WG.getNode id ⦃⇓ x w => ⌜x = n ∧ w = k⌝⦄ := by
  apply (total_iff_run_ambient _ _ _).mpr
  intro w ambient hk
  exact ⟨n, w, ambient, getNode_run w ambient id n (hk ▸ hn), rfl, hk⟩

theorem prefixMatches_wp (k : WG.AipStore) (n : WG.AipNode) (key width : Nat)
    (hw : width = 32 ∨ width = 128) (hn : n.bits < 2 ^ width)
    (hk : key < 2 ^ width) (hc : n.cidr ≤ width) :
    ⦃fun w => ⌜w = k⌝⦄ (WG.prefixMatches n key width : WG.AipM Bool)
    ⦃⇓ x w => ⌜x = decide (prefixBits width n.cidr n.bits =
      prefixBits width n.cidr key) ∧ w = k⌝⦄ := by
  apply (total_iff_run_ambient _ _ _).mpr
  intro w ambient h
  refine ⟨_, w, commonRecords ambient width (n.bits ^^^ key), ?_, rfl, h⟩
  have hlift : (WG.prefixMatches n key width : WG.AipM Bool) =
      StateT.lift (WG.prefixMatches (m := AmbientM) n key width) := by
    change (WG.prefixMatches n key width : WG.AipM Bool) =
      monadLift (WG.prefixMatches (m := AmbientM) n key width)
    simp only [WG.prefixMatches, WG.commonBits, branch, monadLift_self,
      monadLift_bind, monadLift_pure, apply_ite] <;> rfl
  rw [hlift, stateLiftAmbient_run, prefixMatches_run n key width ambient hw hn hk hc]
  rfl

theorem choose_wp (k : WG.AipStore) (n : WG.AipNode) (key : Nat)
    (hc : n.cidr < n.bitlen) :
    ⦃fun w => ⌜w = k⌝⦄ (WG.choose n key : WG.AipM Nat)
    ⦃⇓ x w => ⌜x = bit n.bitlen n.cidr key ∧ w = k⌝⦄ := by
  rw [choose_run n key hc]
  mvcgen

theorem bitAt_wp (k : WG.AipStore) (width : Nat) (parent : WG.Slot) (n : NodeData)
    (l r : Tree) (b : Nat) (hb : b < 2) :
    ⦃fun w => ⌜w = k⌝⦄ ((encode width parent n l r).bitAt b : WG.AipM (Option WG.NodeId))
    ⦃⇓ x w => ⌜x = (Tree.child l r b).root ∧ w = k⌝⦄ := by
  rw [encode_bitAt_run width parent n l r b hb]
  mvcgen

/-- The answer still lies in the current subtree, unless the previous best
match is the winner. There is one iteration reserved for an empty cursor. -/
def SearchState (k : WG.AipStore) (width key : Nat) (answer : Option Nat)
    (remaining : Nat) (node found : Option Nat) (w : WG.AipStore) : Prop :=
  w = k ∧ ∃ parent t, RepAt k.nodes width parent t ∧ t.Valid width ∧
    node = t.root ∧ answer = (t.lookupId width key).or found ∧ t.height + 1 ≤ remaining

/-- Total correctness of the original 130-iteration traversal under a
structurally represented valid tree. Errors have the false postcondition. -/
theorem findNode_wp (k : WG.AipStore) (width key : Nat)
    (hw : width = 32 ∨ width = 128) (hk : key < 2 ^ width)
    (t : Tree) (parent : WG.Slot)
    (hr : RepAt k.nodes width parent t) (hv : t.Valid width) :
    ⦃fun w => ⌜w = k⌝⦄ WG.findNode t.root width key
    ⦃⇓ x w => ⌜x = t.lookupId width key ∧ w = k⌝⦄ := by
  mvcgen [WG.findNode, branch, AmbientM.branch, invariant, AmbientM.invariant]
  invariants
  | inv1 => Invariant.withEarlyReturnNewDo
      (fun cursor state w => ⌜SearchState k width key (t.lookupId width key)
        cursor.suffix.length state.1 state.2 w⌝)
      (fun result _ w => ⌜result = t.lookupId width key ∧ w = k⌝)
      ExceptConds.false
  case vc1.step.h_1 =>
    dsimp +zetaDelta only at *
    rename_i _ _ _ _ _ hnone w ambient hi _
    try simp only [List.cons_ne_nil, and_false, false_and, exists_false, or_false] at hi
    rcases hi.2 with ⟨hkw, p, u, hrep, hvalid, hroot, hans, hbudget⟩
    cases u with
    | empty => simp_all [Tree.root]
    | node n l r => simp [Tree.root] at hroot; grind
  case vc2.step.h_2 =>
    dsimp +zetaDelta only at *
    rename_i _ _ _ _ _ id hsome w ambient hi _
    try simp only [List.cons_ne_nil, and_false, false_and, exists_false, or_false] at hi
    rcases hi.2 with ⟨hkw, p, u, hrep, hvalid, hroot, hans, hbudget⟩
    cases u with
    | empty => simp [Tree.root] at hroot; grind
    | node n l r =>
      have hid : id = n.id := by simpa [Tree.root, hsome] using hroot
      subst id
      have getter := getNode_wp k n.id (encode width p n l r) hrep.1
      have matching := prefixMatches_wp k (encode width p n l r) key width hw
        hvalid.1 hk hvalid.2.1
      mvcgen [getter]
      rename_i fetched current ambient hfetched
      rcases hfetched with ⟨rfl, hcurrent⟩
      mvcgen [matching]
      all_goals try dsimp +zetaDelta only at *
      all_goals try simp_all [encode, Tree.lookupId_node, Tree.root]
      all_goals try mvcgen [WG.choose, WG.AipNode.bitAt, invariant, AmbientM.invariant]
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
    rename_i w ambient hkw
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
tree of either supported family, with the pure answer and unchanged AipStore. -/
theorem findNode_run (w : WG.AipStore) (ambient : Ambient) (width key : Nat)
    (hw : width = 32 ∨ width = 128) (hk : key < 2 ^ width)
    (t : Tree) (parent : WG.Slot)
    (hr : RepAt w.nodes width parent t) (hv : t.Valid width) :
    ∃ w' ambient', ((WG.findNode t.root width key).run w).run ambient =
      .ok ((t.lookupId width key, w'), ambient') ∧ w' = w := by
  obtain ⟨x, w', ambient', he, hx, hframe⟩ := (total_iff_run_ambient _ _ _).mp
    (findNode_wp w width key hw hk t parent hr hv) w ambient rfl
  exact ⟨w', ambient', hx ▸ he, hframe⟩

/-- Successful executions return exactly the identifier selected by the pure
tree. The complete AipStore is preserved; branch records remain in Ambient. -/
theorem findNode_refines (w w' : WG.AipStore) (ambient ambient' : Ambient)
    (width key : Nat) (hw : width = 32 ∨ width = 128) (hk : key < 2 ^ width)
    (t : Tree) (parent : WG.Slot)
    (hr : RepAt w.nodes width parent t) (hv : t.Valid width) (result : Option Nat)
    (hreturn : ((WG.findNode t.root width key).run w).run ambient = .ok ((result, w'), ambient')) :
    result = t.lookupId width key ∧ w' = w := by
  obtain ⟨v, finalAmbient, hex, hframe⟩ := findNode_run w ambient width key hw hk t parent hr hv
  rw [hreturn] at hex
  cases hex
  exact ⟨rfl, hframe⟩

/-- The actual trie adapter carries a successful native lookup back to WGWorld.
Its node-store write-back is the identity because the traversal preserves the
complete AipStore; the recorded Ambient endpoint remains explicit. -/
theorem findNode_lift_run (w : WGWorld) (ambient : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (width key : Nat)
    (hw : width = 32 ∨ width = 128) (hk : key < 2 ^ width)
    (t : Tree) (parent : WG.Slot)
    (hr : RepAt d.nodes width parent t) (hv : t.Valid width) :
    ∃ ambient', ((WG.liftAip (WG.findNode t.root width key)).run w).run ambient =
      .ok ((t.lookupId width key, w), ambient') := by
  let entry : WG.AipStore :=
    { nodes := d.nodes, nextNode := d.nextNode, trie := d.peerAllowedips }
  obtain ⟨finish, ambient', he, hf⟩ := findNode_run entry ambient width key hw hk t parent hr hv
  subst finish
  dsimp only [entry] at he
  refine ⟨ambient', ?_⟩
  rw [liftAip_run, hd]
  simp only [he, Except.map]
  change Except.ok ((_, {w with dev := some d}), ambient') = Except.ok ((_, w), ambient')
  rw [← hd]

end Leanux.Proofs.WG.AllowedIps
