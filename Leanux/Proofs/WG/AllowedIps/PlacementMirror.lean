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
  have comparisonRule {α : Type} (decision : Decision) (value : Bool) (a b : Int)
      (f : Bool → WG.AipM α) (P : WG.AipStore → Prop) (Q : α → WG.AipStore → Prop)
      (h : ⦃fun w => ⌜P w⌝⦄ f value ⦃⇓ r w => ⌜Q r w⌝⦄) :
      ⦃fun w => ⌜P w⌝⦄ ((branchCmp decision value a b : WG.AipM Bool) >>= f)
      ⦃⇓ r w => ⌜Q r w⌝⦄ := by
    apply (total_iff_run_ambient _ _ _).mpr
    intro w ambient hp
    obtain ⟨r, out, finish, hr, hq⟩ := (total_iff_run_ambient _ _ _).mp h w
      {ambient with steps := ambient.steps.push {decision, outcome := value, operands := some (a, b), netRx := ambient.netRxSection}} hp
    exact ⟨r, out, finish, hr, hq⟩
  let range : Std.Legacy.Range := [:130]
  let loopPred (remaining : Nat)
      (state : Option (Option Nat × Bool) × Option Nat × Option Nat)
      (w : WG.AipStore) : Prop :=
    (state.1 = none ∧ PlacementState k width key cidr base t
      remaining state.2.1 state.2.2 w) ∨
    ∃ result, state.1 = some result ∧ remaining = 0 ∧
      w = k ∧ PlacementWitness t width key cidr result
  let inv : Invariant range.toList (Option (Option Nat × Bool) × Option Nat × Option Nat)
      (PostShape.arg WG.AipStore (PostShape.arg Ambient (PostShape.except Stop PostShape.pure))) :=
    ⟨fun p w => ⌜loopPred p.1.suffix.length p.2 w⌝, ExceptConds.false⟩
  unfold WG.nodePlacement
  refine Triple.bind (Q := fun state => inv.1 (⟨range.toList, [], by simp⟩, state)) _ _ ?_ ?_
  · apply Triple.entails_wp_of_pre (Spec.forIn_range inv ?_)
    · intro w ambient hkw
      refine Or.inl ⟨rfl, hkw, .here, t, rfl, trivial, hr, hv, rfl, rfl, ?_⟩
      dsimp only [range]
      simp only [Std.Legacy.Range.toList, List.length_range']
      have height := Tree.height_le hv
      rcases hw with rfl | rfl <;> omega
    · intro pref cur suff h state
      let post (r : ForInStep (Option (Option Nat × Bool) × Option Nat × Option Nat))
          (w : WG.AipStore) :=
        match r with
        | .yield state => loopPred suff.length state w
        | .done state => loopPred 0 state w
      apply Triple.entails_wp_of_post (Q' := PostCond.noThrow
        (ps := PostShape.arg WG.AipStore (PostShape.arg Ambient (PostShape.except Stop PostShape.pure)))
        (fun r w => ⌜post r w⌝))
      · apply (total_iff_run_ambient _ _ _).mpr
        intro w ambient hi
        change loopPred (suff.length + 1) state w at hi
        rcases hi with ⟨hearly, hkw, c, u, hplug, hfollow, hrep, hvalid, hroot, hparent, hbudget⟩ |
          ⟨result, hearly, hlength, hkw, hresult⟩
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
            refine ⟨_, rfl, rfl, hw, c, .empty, hplug, hfollow, ?_⟩
            simpa only [PlacementEnd] using congrArg (fun p => (p, false)) hparent
          | node n l r =>
            simp only [Tree.root] at hroot
            simp only [hroot]
            apply (total_iff_run_ambient _ (fun w => w = k) post).mp ?_ k ambient rfl
            apply branchRule
            simp only [pure_bind]
            refine Triple.bind _ _ (getNode_wp k n.id (encode width (c.slot base) n l r) hrep.1) ?_
            intro fetched
            apply (total_iff_run_ambient _ _ _).mpr
            intro current ambient ⟨hfetched, hcurrent⟩
            subst fetched
            subst current
            apply (total_iff_run_ambient _ (fun w => w = k) post).mp ?_ k ambient rfl
            apply comparisonRule
            dsimp only [encode]
            by_cases hle : n.cidr ≤ cidr
            · simp only [hle, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              refine Triple.bind _ _
                (prefixMatches_wp k (encode width (c.slot base) n l r) key width hw
                  hvalid.1 hk hvalid.2.1) ?_
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
                apply comparisonRule
                by_cases hex : n.cidr = cidr
                · simp only [hex, beq_self_eq_true, ↓reduceIte]
                  apply Triple.pure
                  intro w ambient hw
                  right
                  exact ⟨_, rfl, rfl, hw, c, .node n l r, hplug, hfollow,
                    Or.inr (Or.inr ⟨hex, hm, rfl⟩)⟩
                · simp only [beq_iff_eq, hex, ↓reduceIte]
                  have hlt : n.cidr < cidr := by omega
                  have hwidth : n.cidr < width := by omega
                  have choice := choose_run (m := WG.AipM) (encode width (c.slot base) n l r) key hwidth
                  have child := encode_bitAt_run (m := WG.AipM) width (c.slot base) n l r
                    (bit width n.cidr key) (bit_lt_two width n.cidr key)
                  dsimp only [encode] at choice child
                  rw [choice, pure_bind, child, pure_bind]
                  apply Triple.pure
                  intro w ambient hw
                  left
                  refine ⟨rfl, hw, c.append (Context.edge n l r (bit width n.cidr key)),
                    Tree.child l r (bit width n.cidr key), ?_,
                    hfollow.append (Context.edge_follows n l r hlt hm), ?_,
                    hvalid.child _, rfl, ?_, ?_⟩
                  · simpa only [Context.plug_append, Context.edge_plug] using hplug
                  · simpa only [Context.slot_append, Context.edge_slot n l r (bit_lt_two ..)] using
                      hrep.child (bit_lt_two width n.cidr key)
                  · simp only [Context.lastParent_append, Context.edge_lastParent]
                  · have decrease := Tree.child_height_lt n l r (bit width n.cidr key)
                    omega
              · simp only [hm, decide_false, Bool.not_false, ↓reduceIte]
                apply Triple.pure
                intro w ambient hw
                right
                exact ⟨_, rfl, rfl, hw, c, .node n l r, hplug, hfollow,
                  Or.inr (Or.inl ⟨hle, hm, congrArg (fun p => (p, false)) hparent⟩)⟩
            · simp only [hle, decide_false, Bool.not_false, ↓reduceIte]
              apply Triple.pure
              intro w ambient hw
              right
              exact ⟨_, rfl, rfl, hw, c, .node n l r, hplug, hfollow,
                Or.inl ⟨by omega, congrArg (fun p => (p, false)) hparent⟩⟩
        · omega
      · constructor
        · intro r
          cases r <;> exact SPred.entails.refl _
        · exact ExceptConds.entails.refl _
  · intro state
    apply (total_iff_run_ambient _ _ _).mpr
    intro w ambient hi
    change loopPred 0 state w at hi
    rcases hi with ⟨_, _, c, u, hplug, hfollow, hrep, hvalid, hroot, hparent, hbudget⟩ |
      ⟨result, hearly, hlength, hkw, hresult⟩
    · omega
    · refine ⟨result, w, ambient, ?_, hkw, hresult⟩
      simp only [hearly]
      rfl

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
