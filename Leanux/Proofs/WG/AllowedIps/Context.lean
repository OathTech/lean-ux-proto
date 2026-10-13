import Leanux.Proofs.WG.AllowedIps.StoreMutation

/-! Proof evidence for a hole along an insertion path. Contexts rebuild a
tree; `Tree.insertFresh` remains the sole executable insertion algorithm. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux

inductive Context where
  | here
  | left (n : NodeData) (inner : Context) (right : Tree)
  | right (n : NodeData) (left : Tree) (inner : Context)

def Context.plug : Context → Tree → Tree
  | .here, u => u
  | .left n c r, u => .node n (c.plug u) r
  | .right n l c, u => .node n l (c.plug u)

def Context.append : Context → Context → Context
  | .here, inner => inner
  | .left n c r, inner => .left n (c.append inner) r
  | .right n l c, inner => .right n l (c.append inner)

def Context.slot : Context → WG.Slot → WG.Slot
  | .here, base => base
  | .left n c _, _ => c.slot (.child n.id 0)
  | .right n _ c, _ => c.slot (.child n.id 1)

def Context.lastParent : Context → Option Nat → Option Nat
  | .here, previous => previous
  | .left n c _, _ => c.lastParent (some n.id)
  | .right n _ c, _ => c.lastParent (some n.id)

def Context.Follows (width key cidr : Nat) : Context → Prop
  | .here => True
  | .left n c _ => n.cidr < cidr ∧
      prefixBits width n.cidr n.addr = prefixBits width n.cidr key ∧
      bit width n.cidr key = 0 ∧ c.Follows width key cidr
  | .right n _ c => n.cidr < cidr ∧
      prefixBits width n.cidr n.addr = prefixBits width n.cidr key ∧
      bit width n.cidr key = 1 ∧ c.Follows width key cidr

@[simp] theorem Context.plug_append (c inner : Context) (u : Tree) :
    (c.append inner).plug u = c.plug (inner.plug u) := by
  induction c <;> simp_all [Context.append, Context.plug]

@[simp] theorem Context.slot_append (c inner : Context) (base : WG.Slot) :
    (c.append inner).slot base = inner.slot (c.slot base) := by
  induction c generalizing base <;> simp_all [Context.append, Context.slot]

@[simp] theorem Context.lastParent_append (c inner : Context) (previous : Option Nat) :
    (c.append inner).lastParent previous = inner.lastParent (c.lastParent previous) := by
  induction c generalizing previous <;> simp_all [Context.append, Context.lastParent]

theorem Context.Follows.append {c inner : Context}
    (hc : c.Follows width key cidr) (hi : inner.Follows width key cidr) :
    (c.append inner).Follows width key cidr := by
  induction c <;> simp_all [Context.append, Context.Follows]

theorem Context.focus_rep (c : Context) (u : Tree) (base : WG.Slot)
    (h : RepAt nodes width base (c.plug u)) :
    RepAt nodes width (c.slot base) u := by
  induction c generalizing base with
  | here => exact h
  | left n c r ih => exact ih _ h.2.1
  | right n l c ih => exact ih _ h.2.2

theorem Context.focus_valid (c : Context) (u : Tree) (h : (c.plug u).Valid width) :
    u.Valid width := by
  induction c with
  | here => exact h
  | left n c r ih => exact ih h.2.2.1
  | right n l c ih => exact ih h.2.2.2.1

theorem Context.insertFresh (c : Context) (u : Tree) (fresh peer : Nat)
    (h : c.Follows width key cidr) :
    (c.plug u).insertFresh width fresh key cidr peer =
      let result := u.insertFresh width fresh key cidr peer
      { result with tree := c.plug result.tree } := by
  induction c with
  | here => rfl
  | left n c r ih =>
    rcases h with ⟨hlt, hm, hb, hc⟩
    have hle : n.cidr ≤ cidr := Nat.le_of_lt hlt
    have hne : n.cidr ≠ cidr := Nat.ne_of_lt hlt
    simp [Context.plug, Tree.insertFresh, hle, hne, hm, hb, ih hc]
  | right n l c ih =>
    rcases h with ⟨hlt, hm, hb, hc⟩
    have hle : n.cidr ≤ cidr := Nat.le_of_lt hlt
    have hne : n.cidr ≠ cidr := Nat.ne_of_lt hlt
    simp [Context.plug, Tree.insertFresh, hle, hne, hm, hb, ih hc]

def Context.edge (n : NodeData) (l r : Tree) (b : Nat) : Context :=
  if b = 0 then .left n .here r else .right n l .here

@[simp] theorem Context.edge_plug (n : NodeData) (l r : Tree) (b : Nat) :
    (Context.edge n l r b).plug (Tree.child l r b) = .node n l r := by
  unfold Context.edge Tree.child
  split <;> rfl

@[simp] theorem Context.edge_lastParent (n : NodeData) (l r : Tree) (b : Nat)
    (previous : Option Nat) :
    (Context.edge n l r b).lastParent previous = some n.id := by
  unfold Context.edge
  split <;> rfl

theorem Context.edge_slot (n : NodeData) (l r : Tree) {b : Nat} (hb : b < 2)
    (base : WG.Slot) : (Context.edge n l r b).slot base = .child n.id b := by
  have h : b = 0 ∨ b = 1 := by omega
  rcases h with rfl | rfl <;> rfl

theorem Context.edge_follows (n : NodeData) (l r : Tree)
    (hlt : n.cidr < cidr)
    (hm : prefixBits width n.cidr n.addr = prefixBits width n.cidr key) :
    (Context.edge n l r (bit width n.cidr key)).Follows width key cidr := by
  unfold Context.edge
  split
  · exact ⟨hlt, hm, by assumption, trivial⟩
  · have hb := bit_lt_two width n.cidr key
    exact ⟨hlt, hm, by omega, trivial⟩

/-- The four source exits, retaining the CIDR-before-prefix test order.
Exactness does not require the node to have an owner. -/
def PlacementEnd (width key cidr : Nat) (parent : Option Nat) :
    Tree → (Option Nat × Bool) → Prop
  | .empty, result => result = (parent, false)
  | .node n _ _, result =>
      (cidr < n.cidr ∧ result = (parent, false)) ∨
      (n.cidr ≤ cidr ∧ prefixBits width n.cidr n.addr ≠ prefixBits width n.cidr key ∧
        result = (parent, false)) ∨
      (n.cidr = cidr ∧ prefixBits width n.cidr n.addr = prefixBits width n.cidr key ∧
        result = (some n.id, true))

def PlacementWitness (t : Tree) (width key cidr : Nat) (result : Option Nat × Bool) : Prop :=
  ∃ (c : Context) (u : Tree), t = c.plug u ∧ c.Follows width key cidr ∧
    PlacementEnd width key cidr (c.lastParent none) u result

theorem PlacementEnd.allocations {u : Tree} {result : Option Nat × Bool}
    (h : PlacementEnd width key cidr parent u result) (fresh peer : Nat) :
    result.2 = true ↔ (u.insertFresh width fresh key cidr peer).allocations = 0 := by
  cases u with
  | empty => simp_all [PlacementEnd, Tree.insertFresh, graft]
  | node n l r =>
    rcases h with ⟨hlt, rfl⟩ | ⟨hle, hm, rfl⟩ | ⟨he, hm, rfl⟩
    · have hle : ¬ n.cidr ≤ cidr := by omega
      have hg := graft_allocations width fresh key cidr peer (.node n l r)
      simp only [Tree.insertFresh, hle, false_and, ↓reduceIte, Bool.false_eq_true, false_iff]
      omega
    · have hg := graft_allocations width fresh key cidr peer (.node n l r)
      simp only [Tree.insertFresh, hm, and_false, ↓reduceIte, Bool.false_eq_true, false_iff]
      omega
    · simp_all [Tree.insertFresh]

theorem PlacementWitness.allocations {t : Tree} {result : Option Nat × Bool}
    (h : PlacementWitness t width key cidr result) (fresh peer : Nat) :
    result.2 = true ↔ (t.insertFresh width fresh key cidr peer).allocations = 0 := by
  obtain ⟨c, u, rfl, hf, he⟩ := h
  rw [c.insertFresh u fresh peer hf]
  exact he.allocations fresh peer

theorem PlacementEnd.insertFresh_of_not_exact {u : Tree} {result : Option Nat × Bool}
    (h : PlacementEnd width key cidr parent u result) (hn : result.2 = false)
    (fresh peer : Nat) :
    u.insertFresh width fresh key cidr peer = graft width fresh key cidr peer u := by
  cases u with
  | empty => rfl
  | node n l r =>
    rcases h with ⟨hlt, rfl⟩ | ⟨hle, hm, rfl⟩ | ⟨he, hm, rfl⟩
    · have hle : ¬ n.cidr ≤ cidr := by omega
      simp [Tree.insertFresh, hle]
    · simp [Tree.insertFresh, hm]
    · contradiction

theorem PlacementEnd.graftable {u : Tree} {result : Option Nat × Bool}
    (h : PlacementEnd width key cidr parent u result) (hn : result.2 = false)
    (hv : u.Valid width) (hk : key < 2 ^ width) : Graftable width key cidr u := by
  cases u with
  | empty => trivial
  | node n l r =>
    apply graftable_of_stopped hv hk
    rcases h with ⟨hlt, rfl⟩ | ⟨hle, hm, rfl⟩ | ⟨he, hm, rfl⟩
    · intro ⟨hle, _⟩
      omega
    · exact fun h => hm h.2
    · contradiction

theorem PlacementWitness.stopped {t : Tree} {result : Option Nat × Bool}
    (h : PlacementWitness t width key cidr result) (hn : result.2 = false)
    (hv : t.Valid width) (hk : key < 2 ^ width) :
    ∃ (c : Context) (u : Tree), t = c.plug u ∧ c.Follows width key cidr ∧
      result.1 = c.lastParent none ∧ Graftable width key cidr u ∧
      ∀ fresh peer, t.insertFresh width fresh key cidr peer =
        let localResult := graft width fresh key cidr peer u
        { localResult with tree := c.plug localResult.tree } := by
  obtain ⟨c, u, rfl, hf, he⟩ := h
  refine ⟨c, u, rfl, hf, ?_, he.graftable hn (c.focus_valid u hv) hk, ?_⟩
  · cases u with
    | empty => exact congrArg Prod.fst he
    | node n l r =>
      rcases he with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> simp_all
  · intro fresh peer
    rw [c.insertFresh u fresh peer hf, he.insertFresh_of_not_exact hn fresh peer]

theorem Context.plug_eq_empty {c : Context} {u : Tree} :
    c.plug u = .empty ↔ c = .here ∧ u = .empty := by
  cases c <;> simp [Context.plug]

/-- Any placement witness for a known empty hole returns that hole's parent.
This is uniqueness of structural path evidence, without a new traversal. -/
theorem Context.empty_result (c observed : Context) (u : Tree) (previous : Option Nat)
    (hf : c.Follows width key cidr) (ho : observed.Follows width key cidr)
    (ht : c.plug .empty = observed.plug u)
    (he : PlacementEnd width key cidr (observed.lastParent previous) u result) :
    result = (c.lastParent previous, false) := by
  induction c generalizing observed u previous with
  | here =>
    obtain ⟨rfl, rfl⟩ := Context.plug_eq_empty.mp ht.symm
    exact he
  | left n c r ih =>
    cases observed with
    | here =>
      change Tree.node n (c.plug .empty) r = u at ht
      subst u
      rcases he with ⟨hlt, _⟩ | ⟨_, hm, _⟩ | ⟨heq, _, _⟩
      · have := hf.1; omega
      · exact False.elim (hm hf.2.1)
      · have := hf.1; omega
    | left m inner right =>
      obtain ⟨hn, hl, hr⟩ := Tree.node.inj ht
      subst m
      exact ih inner u (some n.id) hf.2.2.2 ho.2.2.2 hl he
    | right m left inner =>
      have hn := (Tree.node.inj ht).1
      subst m
      have h0 := hf.2.2.1
      have h1 := ho.2.2.1
      omega
  | right n l c ih =>
    cases observed with
    | here =>
      change Tree.node n l (c.plug .empty) = u at ht
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
      exact ih inner u (some n.id) hf.2.2.2 ho.2.2.2 hr he

theorem PlacementWitness.empty_result {c : Context} {result : Option Nat × Bool}
    (hf : c.Follows width key cidr)
    (h : PlacementWitness (c.plug .empty) width key cidr result) :
    result = (c.lastParent none, false) := by
  obtain ⟨observed, u, ht, ho, he⟩ := h
  exact c.empty_result observed u none hf ho ht he

/-- Replacing a focus without changing its root leaves each ancestor's
encoded child pointers unchanged. -/
theorem Context.root_congr (c : Context) {before after : Tree}
    (h : after.root = before.root) : (c.plug after).root = (c.plug before).root := by
  cases c <;> first | exact h | rfl

theorem Context.mem_plug_nodeIds (c : Context) (u : Tree) (id : Nat) :
    id ∈ (c.plug u).nodeIds ↔ id ∈ (c.plug .empty).nodeIds ∨ id ∈ u.nodeIds := by
  induction c with
  | here => simp [Context.plug, Tree.nodeIds]
  | left n c r ih => simp only [Context.plug, Tree.nodeIds, List.mem_cons, List.mem_append, ih]; grind
  | right n l c ih => simp only [Context.plug, Tree.nodeIds, List.mem_cons, List.mem_append, ih]; grind

/-- Exact store replacement at a focus whose node identifier stays fixed.
Only nodes outside the focus must retain their old values. -/
theorem Context.rep_replace_sameRoot (c : Context) (before after : Tree)
    (base : WG.Slot) (hwhole : RepAt nodes width base (c.plug before))
    (hfocus : RepAt nodes' width (c.slot base) after)
    (hroot : after.root = before.root)
    (hframe : ∀ id ∈ (c.plug .empty).nodeIds, nodes'[id]? = nodes[id]?) :
    RepAt nodes' width base (c.plug after) := by
  induction c generalizing base with
  | here => exact hfocus
  | left n c r ih =>
    refine ⟨?_, ih _ hwhole.2.1 hfocus ?_, ?_⟩
    · have he := hframe n.id (by simp [Context.plug, Tree.nodeIds])
      rw [he, hwhole.1]
      simp only [encode, c.root_congr hroot]
    · intro id hi
      exact hframe id (by simp [Context.plug, Tree.nodeIds, hi])
    · exact hwhole.2.2.congr (fun id hi => hframe id (by simp [Context.plug, Tree.nodeIds, hi]))
  | right n l c ih =>
    refine ⟨?_, ?_, ih _ hwhole.2.2 hfocus ?_⟩
    · have he := hframe n.id (by simp [Context.plug, Tree.nodeIds])
      rw [he, hwhole.1]
      simp only [encode, c.root_congr hroot]
    · exact hwhole.2.1.congr (fun id hi => hframe id (by simp [Context.plug, Tree.nodeIds, hi]))
    · intro id hi
      exact hframe id (by simp [Context.plug, Tree.nodeIds, hi])

/-- No identifier of a duplicate-free focus occurs outside that focus. -/
theorem Context.focus_disjoint (c : Context) (u : Tree)
    (hn : (c.plug u).nodeIds.Nodup) :
    ∀ id ∈ u.nodeIds, id ∉ (c.plug .empty).nodeIds := by
  induction c with
  | here => simp [Context.plug, Tree.nodeIds]
  | left n c r ih =>
    simp only [Context.plug, Tree.nodeIds, List.nodup_cons, List.nodup_append] at hn
    intro id hi hout
    have hin := (c.mem_plug_nodeIds u id).mpr (.inr hi)
    simp only [Context.plug, Tree.nodeIds, List.mem_cons, List.mem_append] at hout
    rcases hout with rfl | hc | hr
    · exact hn.1 (List.mem_append_left _ hin)
    · exact ih hn.2.1 id hi hc
    · exact hn.2.2.2 id hin id hr rfl
  | right n l c ih =>
    simp only [Context.plug, Tree.nodeIds, List.nodup_cons, List.nodup_append] at hn
    intro id hi hout
    have hin := (c.mem_plug_nodeIds u id).mpr (.inr hi)
    simp only [Context.plug, Tree.nodeIds, List.mem_cons, List.mem_append] at hout
    rcases hout with rfl | hl | hc
    · exact hn.1 (List.mem_append_right _ hin)
    · exact hn.2.2.2 id hl id hin rfl
    · exact ih hn.2.2.1 id hi hc

theorem Context.focus_nodup (c : Context) (u : Tree)
    (hn : (c.plug u).nodeIds.Nodup) : u.nodeIds.Nodup := by
  induction c with
  | here => exact hn
  | left n c r ih => exact ih (List.nodup_append.mp (List.nodup_cons.mp hn).2).1
  | right n l c ih => exact ih (List.nodup_append.mp (List.nodup_cons.mp hn).2).2.1

end Leanux.Proofs.WG.AllowedIps
