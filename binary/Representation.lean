import Layouts
import Memory
import Leanux.WG.Types

namespace Binary

abbrev Address := BitVec 64

def kindWord : Leanux.WG.IndexKind → BitVec 32
  | .handshake => 1
  | .keypair => 2

/-- Ordered intrusive chain. The head and next fields point to the embedded
    hlist_node, not to the beginning of index_hashtable_entry. Every recursive
    call consumes one list entry, so cycles cannot represent a finite bucket.
    This local loop-shape predicate reads only index, kind and next. It does
    not constrain the owning peer word (including NULL); the whole-world
    relation must separately relate that word and its owning object. -/
def BucketShape (m : Mem 64) :
    Address → List (Address × Leanux.WG.IndexEntry) → Prop
  | head, [] => head = 0
  | head, (a, e) :: rest =>
      a ≠ 0 ∧ head ≠ 0 ∧ head = a + .ofNat 64 Layouts.entry_index_hash ∧
      e.index < 2^32 ∧
      m.loadInt (a + .ofNat 64 Layouts.entry_type) 4 = some (kindWord e.kind).toNat ∧
      m.loadInt (a + .ofNat 64 Layouts.entry_index) 4 = some e.index ∧
      ∃ next, m.loadInt (head + .ofNat 64 Layouts.node_next) 8 = some next.toNat ∧
        BucketShape m next rest

theorem bucket_empty (m : Mem 64) (head : Address) :
    BucketShape m head [] ↔ head = 0 := Iff.rfl

theorem bucket_cons_nonnull (m : Mem 64)
    (head a : Address) (e : Leanux.WG.IndexEntry) (rest)
    (h : BucketShape m head ((a, e) :: rest)) : head ≠ 0 := h.2.1

theorem bucket_tail (m : Mem 64)
    (head a : Address) (e : Leanux.WG.IndexEntry) (rest)
    (h : BucketShape m head ((a, e) :: rest)) :
    ∃ next, m.loadInt (head + .ofNat 64 Layouts.node_next) 8 = some next.toNat ∧
      BucketShape m next rest := h.2.2.2.2.2.2

theorem BucketShape.head_zero_iff {m : Mem 64} {head : Address}
    {es : List (Address × Leanux.WG.IndexEntry)} (h : BucketShape m head es) :
    head = 0 ↔ es = [] := by
  cases es with
  | nil => exact ⟨fun _ => rfl, fun _ => h⟩
  | cons cell rest =>
    constructor
    · exact fun zero => False.elim (h.2.1 zero)
    · intro empty; cases empty

theorem bucket_cons_fields {m : Mem 64} {head a : Address}
    {e : Leanux.WG.IndexEntry} {rest}
    (h : BucketShape m head ((a, e) :: rest)) :
    a ≠ 0 ∧ head = a + .ofNat 64 Layouts.entry_index_hash ∧ e.index < 2^32 ∧
    m.loadInt (a + .ofNat 64 Layouts.entry_type) 4 = some (kindWord e.kind).toNat ∧
    m.loadInt (a + .ofNat 64 Layouts.entry_index) 4 = some e.index :=
  ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

/-- A disjoint write preserves every exact field in the represented chain.
    The premise refers to physical entry bytes, not to a ghost copy of entries. -/
theorem BucketShape.frame
    {before after : Mem 64} {writes : Address → Prop}
    (same : EqualOutside writes before after) (es : List (Address × Leanux.WG.IndexEntry))
    (disjoint : ∀ cell ∈ es, ∀ i < Layouts.entrySize, ¬ writes (cell.1 + .ofNat 64 i))
    (head : Address) (represented : BucketShape before head es) :
    BucketShape after head es := by
  induction es generalizing head with
  | nil => exact represented
  | cons cell es ih =>
    rcases cell with ⟨a, e⟩
    rcases represented with ⟨ha, hh, hnode, hi, kind, index, next, hn, tail⟩
    have unchanged (off n : Nat) (bound : off + n ≤ Layouts.entrySize) :
        before.loadInt (a + .ofNat 64 off) n = after.loadInt (a + .ofNat 64 off) n := by
      apply same.loadInt
      intro i hi
      have h := disjoint (a, e) (by simp) (off + i) (by omega)
      simpa only [BitVec.ofNat_add, BitVec.add_assoc] using h
    refine ⟨ha, hh, hnode, hi, ?_, ?_, next, ?_, ?_⟩
    · exact (unchanged Layouts.entry_type 4 (by decide)).symm.trans kind
    · exact (unchanged Layouts.entry_index 4 (by decide)).symm.trans index
    · rw [hnode] at hn ⊢
      simp only [Layouts.entry_index_hash, Layouts.node_next, BitVec.add_zero] at hn ⊢
      exact (unchanged 8 8 (by decide)).symm.trans hn
    · exact ih (fun cell hc => disjoint cell (by simp [hc])) next tail

#print axioms BucketShape.frame

#print axioms bucket_tail

end Binary
