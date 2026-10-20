import Layouts
import Memory
import Leanux.WG.Types

namespace Binary

abbrev Address := BitVec 64

def kindWord : Leanux.WG.IndexKind → BitVec 32
  | .handshake => 1
  | .keypair => 2

/-- The C mask denotes membership, so order and duplicates in the mirror's
    list of allowed kinds have no physical counterpart. -/
def kindMask (kinds : List Leanux.WG.IndexKind) : BitVec 32 :=
  (if kinds.contains .handshake then 1 else 0) |||
  (if kinds.contains .keypair then 2 else 0)

theorem kindMask_accepts (kinds : List Leanux.WG.IndexKind) (kind : Leanux.WG.IndexKind) :
    decide (kindMask kinds &&& kindWord kind ≠ 0) = kinds.contains kind := by
  cases kind <;>
    cases h : kinds.contains .handshake <;> cases k : kinds.contains .keypair <;>
    simp [kindMask, kindWord, h, k]

/-- Only the C enum bits carry kind membership. Irrelevant high mask bits
    remain unrestricted, as do order and duplicates in the source list. -/
def KindMask (word : BitVec 32) (kinds : List Leanux.WG.IndexKind) : Prop :=
  ∀ kind, decide (word &&& kindWord kind ≠ 0) = kinds.contains kind

theorem kindMask_represents (kinds : List Leanux.WG.IndexKind) :
    KindMask (kindMask kinds) kinds := kindMask_accepts kinds

def maskKinds (word : BitVec 32) : List Leanux.WG.IndexKind :=
  (if decide (word &&& kindWord .handshake ≠ 0) then [.handshake] else []) ++
  (if decide (word &&& kindWord .keypair ≠ 0) then [.keypair] else [])

/-- Every 32-bit mask has a source kind-list representation. -/
theorem maskKinds_represents (word : BitVec 32) : KindMask word (maskKinds word) := by
  intro kind
  cases h : decide (word &&& kindWord .handshake ≠ 0) <;>
    cases k : decide (word &&& kindWord .keypair ≠ 0) <;> cases kind <;>
    simp only [maskKinds, h, k, ite_true, Bool.false_eq_true, ite_false] <;> rfl

#print axioms maskKinds_represents
#print axioms kindMask_represents
#print axioms kindMask_accepts

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

/-- Exactly the three fields read by the lookup loop. The owner peer word
    and hlist pprev word are intentionally absent from this read footprint. -/
def BucketShapeReads (base address : Address) : Prop :=
  InRange (base + 8) 8 address ∨ InRange (base + 24) 4 address ∨
    InRange (base + 28) 4 address

theorem BucketShape.frame_reads {before after : Mem 64} {writes : Address → Prop}
    (same : EqualOutside writes before after) (es : List (Address × Leanux.WG.IndexEntry))
    (disjoint : ∀ cell ∈ es, ∀ address, BucketShapeReads cell.1 address → ¬writes address)
    (head : Address) (represented : BucketShape before head es) :
    BucketShape after head es := by
  induction es generalizing head with
  | nil => exact represented
  | cons cell es ih =>
    rcases cell with ⟨a, e⟩
    rcases represented with ⟨ha, hh, hnode, hi, kind, index, next, hn, tail⟩
    have apart := disjoint (a, e) (by simp)
    refine ⟨ha, hh, hnode, hi, ?_, ?_, next, ?_, ?_⟩
    · exact (same.loadInt _ 4 (fun i hi => apart _ (.inr (.inl ⟨i, hi, rfl⟩)))).symm.trans kind
    · exact (same.loadInt _ 4 (fun i hi => apart _ (.inr (.inr ⟨i, hi, rfl⟩)))).symm.trans index
    · rw [hnode] at hn ⊢
      simp only [Layouts.entry_index_hash, Layouts.node_next, BitVec.add_zero] at hn ⊢
      exact (same.loadInt _ 8 (fun i hi => apart _ (.inl ⟨i, hi, rfl⟩))).symm.trans hn
    · exact ih (fun cell hc => disjoint cell (by simp [hc])) next tail

/-- The mandatory write of peer-get's result does not change the loop's
    fields in that same owning entry, including when the result is NULL. -/
theorem BucketShapeReads.apart_peer (base address : Address)
    (read : BucketShapeReads base address) : ¬InRange base 8 address := by
  rcases read with node | kind | index
  · simpa only [BitVec.add_zero] using
      InRange.offset_disjoint base 8 8 0 8 (by decide) (by decide) (by decide) address node
  · simpa only [BitVec.add_zero] using
      InRange.offset_disjoint base 24 4 0 8 (by decide) (by decide) (by decide) address kind
  · simpa only [BitVec.add_zero] using
      InRange.offset_disjoint base 28 4 0 8 (by decide) (by decide) (by decide) address index

theorem BucketShape.peer_store (memory : Mem 64) (owner : Address) (word : Int)
    (es : List (Address × Leanux.WG.IndexEntry)) (head : Address)
    (represented : BucketShape memory head es)
    (otherEntries : ∀ cell ∈ es, cell.1 ≠ owner →
      ∀ address, BucketShapeReads cell.1 address → ¬InRange owner 8 address) :
    BucketShape (memory.storeInt owner 8 word) head es := by
  apply BucketShape.frame_reads (storeInt_frame memory owner 8 word) es _ head represented
  intro cell member address read
  by_cases own : cell.1 = owner
  · rw [own] at read
    exact read.apart_peer
  · exact otherEntries cell member own address read

#print axioms BucketShape.frame_reads
#print axioms BucketShapeReads.apart_peer
#print axioms BucketShape.peer_store

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
