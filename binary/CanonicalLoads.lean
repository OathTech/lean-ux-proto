import TrustBase

namespace Binary

private theorem allSome_length (xs : List (Option α)) (ys : List α)
    (read : xs.allSome = some ys) : ys.length = xs.length := by
  induction xs generalizing ys with
  | nil => simpa [List.allSome] using congrArg (Option.map List.length) read.symm
  | cons x xs ih =>
    cases x with
    | none => simp [List.allSome, List.mapM_cons] at read
    | some x =>
      cases tail : xs.allSome with
      | none =>
        change List.mapM id xs = none at tail
        simp [List.allSome, List.mapM_cons, tail] at read
      | some rest =>
        have mapped : List.mapM id xs = some rest := tail
        have equal : ys = x :: rest := by
          simpa [List.allSome, List.mapM_cons, mapped] using read.symm
        rw [equal, List.length_cons, List.length_cons, ih rest tail]

theorem loadInt_range (memory : Mem 64) (address : BitVec 64) (width : Nat) (value : Int)
    (read : memory.loadInt address width = some value) :
    0 ≤ value ∧ value < 256 ^ width := by
  cases bytesRead : memory.loadBytes address width with
  | none => simp [Mem.loadInt, bytesRead] at read
  | some bytes =>
    have equal : value = Int.ofBytes bytes := by
      simpa [Mem.loadInt, bytesRead] using read.symm
    have size : bytes.length = width := by
      simpa only [List.length_map, List.length_range] using
        allSome_length _ bytes bytesRead
    rw [equal]
    exact ⟨Int.ofBytes_ge_zero bytes, by simpa only [size] using Int.ofBytes_lt bytes⟩

/-- Kraken's unsigned four-byte read is canonical. The physical KCOV
    invariant already supplies the raw ADD operand; Pre needs no duplicate
    load equation. -/
theorem load32_raw (memory : Mem 64) (address : BitVec 64) (value : BitVec 32)
    (read : TrustBase.load32 memory address = some value) :
    memory.loadInt address 4 = some (value.toNat : Int) := by
  cases raw : memory.loadInt address 4 with
  | none => simp [TrustBase.load32, raw] at read
  | some n =>
    have equal : value = BitVec.ofInt 32 n := by
      simpa [TrustBase.load32, raw] using read.symm
    obtain ⟨nonnegative, bound⟩ := loadInt_range memory address 4 n raw
    rw [equal]
    congr 1
    simp only [BitVec.toNat_ofInt]
    rw [Int.emod_eq_of_lt nonnegative (by simpa using bound), Int.toNat_of_nonneg nonnegative]

#print axioms loadInt_range
#print axioms load32_raw
end Binary
