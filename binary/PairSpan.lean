import PairExcept
import Memory

namespace Binary.Pair

abbrev Span := Nat × Nat

def Span.contains (span : Span) (a : BitVec 64) : Prop := InRange (.ofNat 64 span.1) span.2 a

def spansApart (left right : List Span) : Bool := left.all fun a => right.all fun b =>
  a.1+a.2 ≤ 2^64 && b.1+b.2 ≤ 2^64 && disjointRanges a.1 a.2 b.1 b.2

theorem Span.location {span : Span} {a : BitVec 64} (valid : span.1+span.2 ≤ 2^64)
    (inside : span.contains a) : span.1 ≤ a.toNat ∧ a.toNat < span.1+span.2 := by
  obtain ⟨i,bound,eq⟩ := inside
  have small : span.1+i < 2^64 := by omega
  have raw := congrArg BitVec.toNat eq
  rw [←BitVec.ofNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] at raw
  omega

theorem spansApart_sound {left right : List Span} (ok : spansApart left right = true)
    {l r : Span} (hl : l ∈ left) (hr : r ∈ right) {a : BitVec 64} :
    l.contains a → ¬r.contains a := by
  have checked := List.all_eq_true.mp (List.all_eq_true.mp ok l hl) r hr
  have parts : (l.1+l.2 ≤ 2^64 ∧ r.1+r.2 ≤ 2^64) ∧
      (l.1+l.2 ≤ r.1 ∨ r.1+r.2 ≤ l.1) := by simpa [disjointRanges] using checked
  intro leftAt rightAt
  have := Span.location parts.1.1 leftAt
  have := Span.location parts.1.2 rightAt
  rcases parts.2 with h | h <;> omega

/-- Relate a physical footprint to its executable finite cover once; each
separation check can then discharge all byte-wise non-aliasing premises. -/
def Covers (spans : List Span) (footprint : BitVec 64 → Prop) : Prop :=
  ∀ a, footprint a → ∃ span ∈ spans, span.contains a

theorem spansApart_disjoint {left right : List Span} {P Q : BitVec 64 → Prop}
    (checked : spansApart left right = true) (l : Covers left P) (r : Covers right Q) :
    ∀ a, P a → ¬Q a := by
  intro a hp hq
  obtain ⟨ls,hl,lp⟩ := l a hp
  obtain ⟨rs,hr,rp⟩ := r a hq
  exact spansApart_sound checked hl hr lp rp

theorem Covers.append_left {left right : List Span} {P : BitVec 64 → Prop}
    (cover : Covers left P) : Covers (left ++ right) P := by
  intro a hp
  obtain ⟨s,hs,inside⟩ := cover a hp
  exact ⟨s,List.mem_append_left _ hs,inside⟩

theorem Covers.append_right {left right : List Span} {P : BitVec 64 → Prop}
    (cover : Covers right P) : Covers (left ++ right) P := by
  intro a hp
  obtain ⟨s,hs,inside⟩ := cover a hp
  exact ⟨s,List.mem_append_right _ hs,inside⟩

theorem Covers.range (base : BitVec 64) (size : Nat) :
    Covers [(base.toNat,size)] (InRange base size) := by
  intro a inside
  exact ⟨(base.toNat,size),by simp,by simpa [Span.contains] using inside⟩

end Binary.Pair
