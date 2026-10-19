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
  apply (total_iff_run_ambient _ _ _).mpr
  intro w ambient h
  exact ⟨_, w, ambient, rfl, rfl, h⟩

theorem bitAt_wp (k : WG.AipStore) (width : Nat) (parent : WG.Slot) (n : NodeData)
    (l r : Tree) (b : Nat) (hb : b < 2) :
    ⦃fun w => ⌜w = k⌝⦄ ((encode width parent n l r).bitAt b : WG.AipM (Option WG.NodeId))
    ⦃⇓ x w => ⌜x = (Tree.child l r b).root ∧ w = k⌝⦄ := by
  rw [encode_bitAt_run width parent n l r b hb]
  apply (total_iff_run_ambient _ _ _).mpr
  intro w ambient h
  exact ⟨_, w, ambient, rfl, rfl, h⟩

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
  have branchRule {α : Type} (decision : Decision) (value : Bool)
      (f : Bool → WG.AipM α) (P : WG.AipStore → Prop) (Q : α → WG.AipStore → Prop)
      (h : ⦃fun w => ⌜P w⌝⦄ f value ⦃⇓ r w => ⌜Q r w⌝⦄) :
      ⦃fun w => ⌜P w⌝⦄ ((branch decision value : WG.AipM Bool) >>= f)
      ⦃⇓ r w => ⌜Q r w⌝⦄ := by
    apply (total_iff_run_ambient _ _ _).mpr
    intro w ambient hp
    obtain ⟨r, out, b, hr, hq⟩ := (total_iff_run_ambient _ _ _).mp h w
      {ambient with steps := ambient.steps.push {decision, outcome := value, netRx := ambient.netRxSection}} hp
    exact ⟨r, out, b, hr, hq⟩
  let range : Std.Legacy.Range := [:130]
  let loopPred (remaining : Nat) (state : Option (Option Nat) × Option Nat × Option Nat)
      (w : WG.AipStore) : Prop :=
    (state.1 = none ∧ SearchState k width key (t.lookupId width key)
      remaining state.2.1 state.2.2 w) ∨
    ∃ result, state.1 = some result ∧ remaining = 0 ∧
      result = t.lookupId width key ∧ w = k
  let inv : Invariant range.toList (Option (Option Nat) × Option Nat × Option Nat)
      (PostShape.arg WG.AipStore (PostShape.arg Ambient (PostShape.except Stop PostShape.pure))) :=
    ⟨fun p w => ⌜loopPred p.1.suffix.length p.2 w⌝, ExceptConds.false⟩
  unfold WG.findNode
  refine Triple.bind (Q := fun state => inv.1 (⟨range.toList, [], by simp⟩, state)) _ _ ?_ ?_
  · apply Triple.entails_wp_of_pre (Spec.forIn_range inv ?_)
    · intro w ambient hkw
      refine Or.inl ⟨rfl, hkw, parent, t, hr, hv, rfl, by simp, ?_⟩
      dsimp only [range]
      simp only [Std.Legacy.Range.toList, List.length_range']
      have height := Tree.height_le hv
      rcases hw with rfl | rfl <;> omega
    · intro pref cur suff h state
      let post (r : ForInStep (Option (Option Nat) × Option Nat × Option Nat)) (w : WG.AipStore) :=
        match r with
        | .yield state => loopPred suff.length state w
        | .done state => loopPred 0 state w
      apply Triple.entails_wp_of_post (Q' := PostCond.noThrow
        (ps := PostShape.arg WG.AipStore (PostShape.arg Ambient (PostShape.except Stop PostShape.pure)))
        (fun r w => ⌜post r w⌝))
      · apply (total_iff_run_ambient _ _ _).mpr
        intro w ambient hi
        change loopPred (suff.length + 1) state w at hi
        rcases hi with ⟨hearly, hkw, p, u, hrep, hvalid, hroot, hans, hbudget⟩ |
          ⟨result, hearly, hlength, hresult, hkw⟩
        · subst w
          cases u with
          | empty =>
            simp only [Tree.root] at hroot
            simp only [hroot]
            apply (total_iff_run_ambient _ (fun w => w = k) post).mp ?_ k ambient rfl
            apply branchRule
            apply Triple.pure
            intro w ambient hw
            right
            exact ⟨state.2.2, rfl, rfl, by simpa using hans.symm, hw⟩
          | node n l r =>
            simp only [Tree.root] at hroot
            simp only [hroot]
            apply (total_iff_run_ambient _ (fun w => w = k) post).mp ?_ k ambient rfl
            apply branchRule
            simp only [pure_bind]
            refine Triple.bind _ _ (getNode_wp k n.id (encode width p n l r) hrep.1) ?_
            intro fetched
            apply (total_iff_run_ambient _ _ _).mpr
            intro current ambient ⟨hfetched, hcurrent⟩
            subst fetched
            subst current
            apply (total_iff_run_ambient _ (fun w => w = k) post).mp ?_ k ambient rfl
            refine Triple.bind _ _
              (prefixMatches_wp k (encode width p n l r) key width hw hvalid.1 hk hvalid.2.1) ?_
            intro matching
            apply (total_iff_run_ambient _ _ _).mpr
            intro current ambient ⟨hmatching, hcurrent⟩
            subst matching
            subst current
            apply (total_iff_run_ambient _ (fun w => w = k) post).mp ?_ k ambient rfl
            apply branchRule
            dsimp only [encode]
            by_cases hm : prefixBits width n.cidr n.addr = prefixBits width n.cidr key
            · simp only [hm, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              apply branchRule
              cases hpeer : n.peer.isSome <;> simp only [Bool.false_eq_true, ↓reduceIte]
              all_goals apply branchRule
              all_goals by_cases hc : n.cidr = width
              all_goals simp only [hc, beq_self_eq_true, beq_iff_eq, ↓reduceIte]
              all_goals first
                | (apply Triple.pure
                   intro w ambient hw
                   right
                   refine ⟨_, rfl, rfl, ?_, hw⟩
                   rw [Tree.lookupId_node, ite_eq_left hm, ite_eq_left hc] at hans
                   simpa [hpeer] using hans.symm)
                | (have hlt : n.cidr < width := by
                     have bound := hvalid.2.1
                     omega
                   have choice := choose_run (m := WG.AipM) (encode width p n l r) key hlt
                   have child := encode_bitAt_run (m := WG.AipM) width p n l r
                     (bit width n.cidr key) (bit_lt_two width n.cidr key)
                   dsimp only [encode] at choice child
                   rw [choice, pure_bind, child, pure_bind]
                   apply Triple.pure
                   intro w ambient hw
                   left
                   refine ⟨rfl, hw, .child n.id (bit width n.cidr key),
                     Tree.child l r (bit width n.cidr key),
                     hrep.child (bit_lt_two ..), hvalid.child _, rfl, ?_, ?_⟩
                   · rw [Tree.lookupId_node, ite_eq_left hm, ite_eq_right hc] at hans
                     simpa [hpeer, Option.or_assoc] using hans
                   · have decrease := Tree.child_height_lt n l r (bit width n.cidr key)
                     omega)
            · simp only [hm, decide_false, Bool.not_false, ↓reduceIte]
              apply Triple.pure
              intro w ambient hw
              right
              exact ⟨state.2.2, rfl, rfl, by simpa [Tree.lookupId_node, hm] using hans.symm, hw⟩
        · omega
      · constructor
        · intro r
          cases r <;> exact SPred.entails.refl _
        · exact ExceptConds.entails.refl _
  · intro state
    apply (total_iff_run_ambient _ _ _).mpr
    intro w ambient hi
    change loopPred 0 state w at hi
    rcases hi with ⟨_, _, p, u, hrep, hvalid, hroot, hans, hbudget⟩ |
      ⟨result, hearly, hlength, hresult, hkw⟩
    · omega
    · refine ⟨result, w, ambient, ?_, hresult, hkw⟩
      simp only [hearly]
      rfl

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
