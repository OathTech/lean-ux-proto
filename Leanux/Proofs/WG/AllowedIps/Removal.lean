import Leanux.Proofs.WG.AllowedIps.Insertion
import Init.Data.List.Sublist

/-!
# Pure Patricia removal

Erasing an identifier clears its owned entry and contracts ownerless nodes
with at most one child. The exact entry and identifier laws hold on arbitrary
trees. Compression and distinct node identifiers make this normalization local
to the source's target and, at most, its immediate parent. Original mutation
refinement and peer-list history are separate obligations.
-/
namespace Leanux.Proofs.WG.AllowedIps

def Tree.compact (n : NodeData) (l r : Tree) : Tree :=
  match n.peer, l, r with
  | none, .empty, _ => r
  | none, _, .empty => l
  | _, _, _ => .node n l r

def Tree.eraseId (id : Nat) : Tree → Tree
  | .empty => .empty
  | .node n l r =>
      compact (if n.id = id then { n with peer := none } else n)
        (l.eraseId id) (r.eraseId id)

theorem Tree.compact_entries (n : NodeData) (l r : Tree) :
    (compact n l r).entries = n.entries ++ l.entries ++ r.entries := by
  cases hp : n.peer <;> cases l <;> cases r <;>
    simp [compact, hp, Tree.entries, NodeData.entries, NodeData.own]

theorem Tree.compact_nodeIds (n : NodeData) (l r : Tree) :
    (compact n l r).nodeIds.Sublist (Tree.node n l r).nodeIds := by
  cases hp : n.peer <;> cases l <;> cases r <;>
    simp only [compact, hp, Tree.nodeIds, List.nil_append, List.append_nil] <;>
    first | exact .refl _ | exact List.sublist_cons_self _ _

theorem Tree.compact_compressed {n : NodeData} {l r : Tree}
    (hl : l.Compressed) (hr : r.Compressed) : (compact n l r).Compressed := by
  cases hp : n.peer <;> cases l <;> cases r <;>
    simp_all [compact, Tree.Compressed, Tree.root]

theorem Tree.compact_eq {n : NodeData} {l r : Tree}
    (hc : (Tree.node n l r).Compressed) : compact n l r = .node n l r := by
  cases hp : n.peer <;> cases l <;> cases r <;>
    simp_all [compact, Tree.Compressed, Tree.root]

theorem Tree.compact_valid {n : NodeData} {l r : Tree}
    (hv : (Tree.node n l r).Valid width) : (compact n l r).Valid width := by
  cases hp : n.peer <;> cases l <;> cases r <;>
    simp_all [compact, Tree.Valid, Child]

/-- A promoted descendant stays on the same side of every enclosing parent. -/
theorem Child.promote {parent n : NodeData} {l r child : Tree}
    (outer : Child width parent side (.node n l r))
    (inner : Child width n branchBit child) (hv : child.Valid width) :
    Child width parent side child := by
  cases child with
  | empty => trivial
  | node c cl cr =>
    have hn : n.cidr ≤ width := Nat.le_trans (Nat.le_of_lt inner.1) hv.2.1
    exact ⟨Nat.lt_trans outer.1 inner.1,
      (prefix_eq_of_le (Nat.le_of_lt outer.1) hn inner.2.1).trans outer.2.1,
      (bit_eq_of_prefix_eq outer.1 hn inner.2.1).trans outer.2.2⟩

theorem Tree.compact_child {parent n : NodeData} {l r : Tree}
    (hv : (Tree.node n l r).Valid width)
    (he : Child width parent side (.node n l r)) :
    Child width parent side (compact n l r) := by
  cases hp : n.peer with
  | some p => simpa [compact, hp] using he
  | none =>
    cases l with
    | empty => simpa [compact, hp] using he.promote hv.2.2.2.2.2 hv.2.2.2.1
    | node a al ar =>
      cases r with
      | empty => simpa [compact, hp] using he.promote hv.2.2.2.2.1 hv.2.2.1
      | node b bl br => simpa [compact, hp] using he

theorem NodeData.erase_entries (n : NodeData) (id : Nat) :
    (if n.id = id then {n with peer := none} else n).entries =
      n.entries.filter (fun e => e.id != id) := by
  by_cases hi : n.id = id <;> cases hp : n.peer <;>
    simp [hi, hp, NodeData.entries, NodeData.own, NodeData.entry]

/-- Exact ordered filtering, without validity, compression or ID uniqueness. -/
theorem Tree.eraseId_entries (t : Tree) (id : Nat) :
    (t.eraseId id).entries = t.entries.filter (fun e => e.id != id) := by
  induction t with
  | empty => rfl
  | node n l r ihl ihr =>
    simp only [eraseId, compact_entries, NodeData.erase_entries, ihl, ihr,
      Tree.entries, List.filter_append]

theorem Tree.eraseId_nodeIds (t : Tree) (id : Nat) :
    (t.eraseId id).nodeIds.Sublist t.nodeIds := by
  induction t with
  | empty => exact .refl _
  | node n l r ihl ihr =>
    apply (compact_nodeIds _ _ _).trans
    have h := (ihl.append ihr).cons_cons n.id
    by_cases hi : n.id = id <;> simpa [Tree.nodeIds, hi] using h

theorem Tree.eraseId_compressed (t : Tree) (id : Nat) : (t.eraseId id).Compressed := by
  induction t with
  | empty => trivial
  | node n l r ihl ihr => exact compact_compressed ihl ihr

theorem Tree.eraseId_valid_child {t : Tree} (hv : t.Valid width) (id : Nat) :
    (t.eraseId id).Valid width ∧
      ∀ parent side, Child width parent side t → Child width parent side (t.eraseId id) := by
  induction t with
  | empty => exact ⟨trivial, fun _ _ _ => trivial⟩
  | node n l r ihl ihr =>
    obtain ⟨vl, el⟩ := ihl hv.2.2.1
    obtain ⟨vr, er⟩ := ihr hv.2.2.2.1
    have v : (Tree.node n (l.eraseId id) (r.eraseId id)).Valid width :=
      ⟨hv.1, hv.2.1, vl, vr, el n 0 hv.2.2.2.2.1, er n 1 hv.2.2.2.2.2⟩
    by_cases hi : n.id = id
    · have v' : (Tree.node {n with peer := none} (l.eraseId id) (r.eraseId id)).Valid width := v
      refine ⟨by simpa [eraseId, hi] using compact_valid v', ?_⟩
      intro parent side he
      have he' : Child width parent side (.node {n with peer := none} (l.eraseId id) (r.eraseId id)) := he
      simpa [eraseId, hi] using compact_child v' he'
    · refine ⟨by simpa [eraseId, hi] using compact_valid v, ?_⟩
      intro parent side he
      have he' : Child width parent side (.node n (l.eraseId id) (r.eraseId id)) := he
      simpa [eraseId, hi] using compact_child v he'

theorem Tree.eraseId_valid {t : Tree} (hv : t.Valid width) (id : Nat) :
    (t.eraseId id).Valid width := (eraseId_valid_child hv id).1

theorem Tree.eraseId_child {t : Tree} (hv : t.Valid width)
    (he : Child width parent side t) (id : Nat) :
    Child width parent side (t.eraseId id) := (eraseId_valid_child hv id).2 parent side he

theorem Tree.eraseId_absent {t : Tree} {id : Nat} (hc : t.Compressed) (hi : id ∉ t.nodeIds) :
    t.eraseId id = t := by
  induction t with
  | empty => rfl
  | node n l r ihl ihr =>
    have hn : n.id ≠ id := fun he => hi (by simp [Tree.nodeIds, he])
    have hl : id ∉ l.nodeIds := fun h => hi (by simp [Tree.nodeIds, h])
    have hr : id ∉ r.nodeIds := fun h => hi (by simp [Tree.nodeIds, h])
    simpa only [eraseId, ite_eq_right hn, ihl hc.1 hl, ihr hc.2.1 hr] using compact_eq hc

theorem Tree.eraseId_nodup {t : Tree} (hn : t.nodeIds.Nodup) (id : Nat) :
    (t.eraseId id).nodeIds.Nodup := hn.sublist (eraseId_nodeIds t id)

theorem Tree.eraseId_bounded {t : Tree} (hb : ∀ j ∈ t.nodeIds, j < frontier) (id : Nat) :
    ∀ j ∈ (t.eraseId id).nodeIds, j < frontier :=
  fun j hj => hb j ((eraseId_nodeIds t id).subset hj)

theorem Tree.eraseId_lookup_spec {t : Tree} (hv : t.Valid width) (id key : Nat) :
    Winner width key (t.entries.filter (fun e => e.id != id))
      ((t.eraseId id).lookup width key) := by
  rw [← eraseId_entries]
  exact lookup_spec (eraseId_valid hv id) key

@[simp] theorem Tree.root_isSome_iff (t : Tree) : t.root.isSome ↔ t ≠ .empty := by
  cases t <;> simp [Tree.root]

theorem Tree.compact_eq_empty {n : NodeData} {l r : Tree} :
    compact n l r = .empty ↔ n.peer = none ∧ l = .empty ∧ r = .empty := by
  cases hp : n.peer <;> cases l <;> cases r <;> simp [compact, hp]

/-- At a unique target, descendants are untouched; only its ownership is cleared. -/
theorem Tree.eraseId_at_root {n : NodeData} {l r : Tree}
    (hc : (Tree.node n l r).Compressed) (hn : (Tree.node n l r).nodeIds.Nodup) :
    (Tree.node n l r).eraseId n.id = compact {n with peer := none} l r := by
  have hl : n.id ∉ l.nodeIds := fun h => (List.nodup_cons.mp hn).1 (List.mem_append_left _ h)
  have hr : n.id ∉ r.nodeIds := fun h => (List.nodup_cons.mp hn).1 (List.mem_append_right _ h)
  simp only [eraseId, ite_true, eraseId_absent hc.1 hl, eraseId_absent hc.2.1 hr]

/-- Under the source structural invariants, only a targeted leaf can vanish
completely. In particular, promoting a child cannot empty another ancestor. -/
theorem Tree.eraseId_empty_iff {t : Tree} (hc : t.Compressed) (hn : t.nodeIds.Nodup)
    (id : Nat) : t.eraseId id = .empty ↔
      t = .empty ∨ ∃ n, t = .node n .empty .empty ∧ n.id = id := by
  induction t with
  | empty => simp [eraseId]
  | node n l r ihl ihr =>
    have nh := List.nodup_cons.mp hn
    have nd := List.nodup_append.mp nh.2
    by_cases hi : n.id = id
    · subst id
      rw [eraseId_at_root hc hn, compact_eq_empty]
      simp only [true_and, reduceCtorEq, false_or, node.injEq]
      constructor
      · rintro ⟨hl, hr⟩
        exact ⟨n, ⟨rfl, hl, hr⟩, rfl⟩
      · rintro ⟨a, ⟨he, hl, hr⟩, _⟩
        exact ⟨hl, hr⟩
    · have el := ihl hc.1 nd.1
      have er := ihr hc.2.1 nd.2.1
      have notEmpty : (Tree.node n l r).eraseId id ≠ .empty := by
        intro he
        rw [eraseId, ite_eq_right hi, compact_eq_empty] at he
        have ln := (hc.2.2 he.1).1
        have rn := (hc.2.2 he.1).2
        obtain ⟨a, ha, hid⟩ := (el.mp he.2.1).resolve_left (root_isSome_iff _ |>.mp ln)
        obtain ⟨b, hb, hjd⟩ := (er.mp he.2.2).resolve_left (root_isSome_iff _ |>.mp rn)
        have ila : id ∈ l.nodeIds := by simp [ha, Tree.nodeIds, hid]
        have irb : id ∈ r.nodeIds := by simp [hb, Tree.nodeIds, hjd]
        exact nd.2.2 id ila id irb rfl
      simp only [notEmpty, false_iff, reduceCtorEq, false_or, node.injEq]
      rintro ⟨a, ⟨he, _, _⟩, hid⟩
      exact hi (he ▸ hid)

theorem Tree.eraseId_binary {n : NodeData} {l r : Tree}
    (hc : (Tree.node n l r).Compressed) (hn : (Tree.node n l r).nodeIds.Nodup)
    (hl : l.root.isSome) (hr : r.root.isSome) :
    (Tree.node n l r).eraseId n.id = .node {n with peer := none} l r := by
  rw [eraseId_at_root hc hn]
  cases l <;> cases r <;> simp_all [Tree.root, compact]

theorem Tree.eraseId_unary_left {n : NodeData} {l : Tree}
    (hc : (Tree.node n l .empty).Compressed) (hn : (Tree.node n l .empty).nodeIds.Nodup) :
    (Tree.node n l .empty).eraseId n.id = l := by
  rw [eraseId_at_root hc hn]
  cases l <;> rfl

theorem Tree.eraseId_unary_right {n : NodeData} {r : Tree}
    (hc : (Tree.node n .empty r).Compressed) (hn : (Tree.node n .empty r).nodeIds.Nodup) :
    (Tree.node n .empty r).eraseId n.id = r := by
  rw [eraseId_at_root hc hn]
  rfl

@[simp] theorem Tree.eraseId_leaf (n : NodeData) :
    (Tree.node n .empty .empty).eraseId n.id = .empty := by
  simp [eraseId, compact]

theorem Tree.compact_length (n : NodeData) (l r : Tree) :
    l.nodeIds.length + r.nodeIds.length ≤ (compact n l r).nodeIds.length := by
  cases hp : n.peer <;> cases l <;> cases r <;>
    simp [compact, hp, Tree.nodeIds, List.length_append] <;> omega

/-- At most two node identifiers disappear after one unique target is erased.
The local/context equations separately identify the affected nodes. This pure
cardinality bound does not count original freeNode calls. -/
theorem Tree.eraseId_retired_le_two {t : Tree} (hc : t.Compressed)
    (hn : t.nodeIds.Nodup) (id : Nat) :
    t.nodeIds.length ≤ (t.eraseId id).nodeIds.length + 2 := by
  induction t with
  | empty => simp [Tree.nodeIds]
  | node n l r ihl ihr =>
    have nh := List.nodup_cons.mp hn
    have nd := List.nodup_append.mp nh.2
    by_cases hi : n.id = id
    · subst id
      rw [eraseId_at_root hc hn]
      have h := compact_length {n with peer := none} l r
      simp only [Tree.nodeIds, List.length_cons, List.length_append]
      omega
    · simp only [eraseId, ite_eq_right hi]
      by_cases hl : id ∈ l.nodeIds
      · have hr : id ∉ r.nodeIds := fun h => nd.2.2 id hl id h rfl
        rw [eraseId_absent hc.2.1 hr]
        by_cases he : l.eraseId id = .empty
        · have ln : l ≠ .empty := by intro h; simp [h, Tree.nodeIds] at hl
          obtain ⟨a, ha, _⟩ := ((eraseId_empty_iff hc.1 nd.1 id).mp he).resolve_left ln
          have h := compact_length n (l.eraseId id) r
          simp only [he, Tree.nodeIds, List.length_nil, Nat.zero_add] at h
          rw [he]
          simp only [ha, Tree.nodeIds, List.length_cons, List.length_append, List.length_nil]
          omega
        · have vc : (Tree.node n (l.eraseId id) r).Compressed :=
            ⟨eraseId_compressed l id, hc.2.1,
              fun hp => ⟨(root_isSome_iff _).mpr he, (hc.2.2 hp).2⟩⟩
          rw [compact_eq vc]
          have h := ihl hc.1 nd.1
          simp only [Tree.nodeIds, List.length_cons, List.length_append]
          omega
      · rw [eraseId_absent hc.1 hl]
        by_cases he : r.eraseId id = .empty
        · rcases (eraseId_empty_iff hc.2.1 nd.2.1 id).mp he with hr | ⟨a, ha, _⟩
          · have h := compact_length n l (r.eraseId id)
            simp only [hr, Tree.nodeIds, List.length_nil] at *
            simp only [List.length_cons, List.length_append, List.length_nil, Nat.add_zero]
            omega
          · have h := compact_length n l (r.eraseId id)
            simp only [he, Tree.nodeIds, List.length_nil, Nat.add_zero] at h
            rw [he]
            simp only [ha, Tree.nodeIds, List.length_cons, List.length_append, List.length_nil]
            omega
        · have vc : (Tree.node n l (r.eraseId id)).Compressed :=
            ⟨hc.1, eraseId_compressed r id,
              fun hp => ⟨(hc.2.2 hp).1, (root_isSome_iff _).mpr he⟩⟩
          rw [compact_eq vc]
          have h := ihr hc.2.1 nd.2.1
          simp only [Tree.nodeIds, List.length_cons, List.length_append]
          omega

theorem Tree.eraseId_leaf_left {parent n : NodeData} {sibling : Tree}
    (hc : (Tree.node parent (.node n .empty .empty) sibling).Compressed)
    (hn : (Tree.node parent (.node n .empty .empty) sibling).nodeIds.Nodup) :
    (Tree.node parent (.node n .empty .empty) sibling).eraseId n.id =
      compact parent .empty sibling := by
  have nh := List.nodup_cons.mp hn
  have nd := List.nodup_append.mp nh.2
  have hne : parent.id ≠ n.id := fun he => nh.1 (by simp [Tree.nodeIds, he])
  have hs : n.id ∉ sibling.nodeIds := fun h =>
    nd.2.2 n.id (by simp [Tree.nodeIds]) n.id h rfl
  rw [eraseId, ite_eq_right hne, eraseId_leaf, eraseId_absent hc.2.1 hs]

theorem Tree.eraseId_leaf_right {parent n : NodeData} {sibling : Tree}
    (hc : (Tree.node parent sibling (.node n .empty .empty)).Compressed)
    (hn : (Tree.node parent sibling (.node n .empty .empty)).nodeIds.Nodup) :
    (Tree.node parent sibling (.node n .empty .empty)).eraseId n.id =
      compact parent sibling .empty := by
  have nh := List.nodup_cons.mp hn
  have nd := List.nodup_append.mp nh.2
  have hne : parent.id ≠ n.id := fun he => nh.1 (by simp [Tree.nodeIds, he])
  have hs : n.id ∉ sibling.nodeIds := fun h =>
    nd.2.2 n.id h n.id (by simp [Tree.nodeIds]) rfl
  rw [eraseId, ite_eq_right hne, eraseId_leaf, eraseId_absent hc.1 hs]

/-- A targeted leaf either leaves its owned parent in place or promotes
the sibling of an ownerless parent. Compression makes that sibling nonempty. -/
theorem Tree.eraseId_leaf_parent {parent n : NodeData} {sibling : Tree} {side : Nat}
    (hc : (Tree.fork parent side (.node n .empty .empty) sibling).Compressed)
    (hn : (Tree.fork parent side (.node n .empty .empty) sibling).nodeIds.Nodup) :
    (Tree.fork parent side (.node n .empty .empty) sibling).eraseId n.id =
      if parent.peer = none then sibling else Tree.fork parent side .empty sibling := by
  by_cases hs : side = 0
  · simp only [Tree.fork, ite_eq_left hs] at *
    rw [eraseId_leaf_left hc hn]
    cases hp : parent.peer <;> cases sibling <;> simp [compact, hp]
  · simp only [Tree.fork, ite_eq_right hs] at *
    rw [eraseId_leaf_right hc hn]
    cases hp : parent.peer <;> cases sibling <;> simp [compact, hp]

end Leanux.Proofs.WG.AllowedIps
