import C1Interfaces
import MemoryBytes
import StackFrame

/-! Result C1, work package 3, rollback: byte-level helpers. Two memories
that load the same word at an address hold the same bytes there; ranges at
natural addresses that do not meet as intervals do not meet as footprints. -/
namespace Binary.Statements.C1.Proof.Undo
open Binary.Pair Binary.TrustBase

/-- Intervals of natural addresses that are apart are apart as footprints. -/
theorem range_apart {a n b k : Nat} (first : a+n ≤ 2^64) (second : b+k ≤ 2^64)
    (apart : a+n ≤ b ∨ b+k ≤ a) :
    ∀ x, InRange (.ofNat 64 a) n x → ¬InRange (.ofNat 64 b) k x := by
  intro x left right
  have l := Span.location (span := (a,n)) first left
  have r := Span.location (span := (b,k)) second right
  dsimp only at l r
  omega

/-- A slice of a range is inside the range. -/
theorem range_slice {base offset size n : Nat} (within : offset+size ≤ n) {x : BitVec 64}
    (inside : InRange (.ofNat 64 (base+offset)) size x) : InRange (.ofNat 64 base) n x := by
  obtain ⟨i,bound,at_⟩ := inside
  exact ⟨offset+i,by omega,by rw [at_,BitVec.ofNat_add,BitVec.ofNat_add,BitVec.add_assoc]⟩

/-- Loads see only the bytes of their range. -/
theorem loadInt_bytes_congr {m m' : DataMem} (address : BitVec 64) (size : Nat)
    (same : ∀ i < size, m.get? (address + .ofNat 64 i) = m'.get? (address + .ofNat 64 i)) :
    m.loadInt address size = m'.loadInt address size := by
  have outside : EqualOutside (fun y => m.get? y ≠ m'.get? y) m m' := fun y h => Classical.not_not.mp h
  exact outside.loadInt address size (fun i bound differ => differ (same i bound))

/-- Two memories that load the same value at an address agree on its bytes. -/
theorem bytes_of_words {m m' : DataMem} {address : BitVec 64} {size : Nat} {value : Int}
    (first : m.loadInt address size = some value) (second : m'.loadInt address size = some value)
    {x : BitVec 64} (inside : InRange address size x) : m.get? x = m'.get? x := by
  obtain ⟨i,bound,at_⟩ := inside
  rw [at_,MemoryBytes.get_of_loadInt m address size value first i bound,
    MemoryBytes.get_of_loadInt m' address size value second i bound]

/-- A stored word reads back, as a natural number below 2^64. -/
theorem load_store_nat (m : DataMem) (address : BitVec 64) {value : Nat} (small : value < 2^64) :
    (m.storeInt address 8 (BitVec.ofNat 64 value).toInt).loadInt address 8 = some (value : Int) := by
  have read := load64_store m address (BitVec.ofNat 64 value)
  rwa [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] at read

#print axioms bytes_of_words
#print axioms range_apart
end Binary.Statements.C1.Proof.Undo
