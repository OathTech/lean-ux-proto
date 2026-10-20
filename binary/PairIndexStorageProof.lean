import PairIndexStorage
import PairIndexNames

namespace Binary.Pair.Index

theorem storage_apart {n o} (checked : storageCheck n o=true) {left right : Span}
    (l : left ∈ storageSpans n o) (r : right ∈ storageSpans n o) (different : left≠right) :
    left.1+left.2≤right.1 ∨ right.1+right.2≤left.1 := by
  have separate : separated (storageSpans n o)=true :=
    (show _ ∧ _ from by simpa only [storageCheck,Bool.and_eq_true] using checked).2
  have pairs := separated_sound separate
  have apart := Trie.pairwise_mem_ne (R := fun a b : Span => disjointRanges a.1 a.2 b.1 b.2=true)
    (fun a b h => by simpa only [disjointRanges,Bool.or_comm] using h) pairs l r different
  simpa only [disjointRanges,Bool.or_eq_true,decide_eq_true_eq] using apart

/-- Slices of separate allocations are separate; within one allocation the
caller supplies only arithmetic on the two field offsets. -/
theorem storage_slices_apart {n o} (checked : storageCheck n o=true)
    {left right : Span} (l : left ∈ storageSpans n o) (r : right ∈ storageSpans n o)
    {a size b otherSize : Nat}
    (li : left.1≤a ∧ a+size≤left.1+left.2)
    (ri : right.1≤b ∧ b+otherSize≤right.1+right.2)
    (same : left=right → a+size≤b ∨ b+otherSize≤a) :
    ∀ address, InRange (.ofNat 64 a) size address → ¬InRange (.ofNat 64 b) otherSize address := by
  have lb := storage_bounds checked l
  have rb := storage_bounds checked r
  have numeric : a+size≤b ∨ b+otherSize≤a := by
    by_cases equal : left=right
    · exact same equal
    · rcases storage_apart checked l r equal with first | second
      · exact .inl (by omega)
      · exact .inr (by omega)
  intro address first second
  have := Span.location (span := (a,size)) (by omega) first
  have := Span.location (span := (b,otherSize)) (by omega) second
  rcases numeric with first | second <;> omega

theorem entry_bound {n o owner base} (checked : storageCheck n o=true)
    (named : (owner,base) ∈ n.owners) : base+o.entrySize≤2^64 :=
  (storage_bounds checked (entry_storage named)).2

theorem entry_fields_apart {n o owner base other otherBase}
    (checked : storageCheck n o=true) (named : (owner,base) ∈ n.owners)
    (otherNamed : (other,otherBase) ∈ n.owners)
    {offset size otherOffset otherSize : Nat}
    (within : offset+size≤o.entrySize) (otherWithin : otherOffset+otherSize≤o.entrySize)
    (different : base=otherBase → offset+size≤otherOffset ∨ otherOffset+otherSize≤offset) :
    ∀ address, InRange (.ofNat 64 (base+offset)) size address →
      ¬InRange (.ofNat 64 (otherBase+otherOffset)) otherSize address := by
  apply storage_slices_apart checked (entry_storage named) (entry_storage otherNamed)
    ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  intro same
  have bases := congrArg Prod.fst same
  rcases different bases with first | second
  · exact .inl (by omega)
  · exact .inr (by omega)

#print axioms storage_slices_apart
#print axioms entry_fields_apart
end Binary.Pair.Index
