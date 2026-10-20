import PairWordStore
import PairSpan

namespace Binary.Pair

/-- A straight-line memory effect with the instruction order retained.
Aliasing destinations are allowed; the last write to a word wins. -/
def writeWords (m : DataMem) (writes : List (Nat × Nat)) : DataMem :=
  writes.foldl (fun m (a,value) => write64 m a value) m

def readWords (writes : List (Nat × Nat)) (address : Nat) (initial : Decode Nat) : Decode Nat :=
  writes.foldl (fun old (a,value) => if address=a then .ok value else old) initial

/-- Distinct words must be byte-disjoint; equal destinations are kept and
resolved by write order. No alignment restriction is imposed by this lemma. -/
theorem word_writeWords (m : DataMem) (writes : List (Nat × Nat)) (path : String) (address : Nat)
    (bound : address+8≤2^64)
    (values : ∀ p ∈ writes, p.2<2^64)
    (apart : ∀ p ∈ writes, address≠p.1 → ∀ a,
      InRange (.ofNat 64 address) 8 a → ¬InRange (.ofNat 64 p.1) 8 a) :
    word (writeWords m writes) path address 8=readWords writes address (word m path address 8) := by
  induction writes generalizing m with
  | nil => rfl
  | cons p writes ih =>
    have rest := ih (write64 m p.1 p.2) (fun q member => values q (by simp [member]))
      (fun q member => apart q (by simp [member]))
    change word (writeWords (write64 m p.1 p.2) writes) path address 8=_
    rw [rest,word_write64 m path address p.1 p.2 bound (values p (by simp)) (apart p (by simp))]
    rfl

def WordWrites (writes : List (Nat × Nat)) (a : BitVec 64) : Prop :=
  ∃ p ∈ writes, InRange (.ofNat 64 p.1) 8 a

theorem writeWords_frame (m : DataMem) (writes : List (Nat × Nat)) :
    EqualOutside (WordWrites writes) m (writeWords m writes) := by
  induction writes generalizing m with
  | nil => exact fun _ _ => rfl
  | cons p writes ih =>
    intro a outside
    have first := write64_frame m p.1 p.2 a (fun inside => outside ⟨p,by simp,inside⟩)
    have rest := ih (write64 m p.1 p.2) a (by
      rintro ⟨q,member,inside⟩
      exact outside ⟨q,by simp [member],inside⟩)
    exact first.trans rest

#print axioms word_writeWords
#print axioms writeWords_frame
end Binary.Pair
