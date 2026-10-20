import Leanux.WG.AllowedIps
import Kraken.X64.Semantics

namespace Binary.CommonBits

/-- BSR returns a zero-based highest-set-bit index. Linux seeds the zero
    case with -1 and adds one in 32 bits, implementing fls for either width. -/
def seededScan (x : Nat) : BitVec 32 :=
  if x = 0 then 0xffffffff else .ofNat 32 x.log2

theorem seededScan_fls (x : Nat) (bound : x < 2^128) :
    (seededScan x + 1).toNat = Leanux.WG.fls x := by
  by_cases zero : x = 0
  · subst x; decide
  · have small : x.log2 < 128 := (Nat.log2_lt zero).mpr bound
    simp only [seededScan, ↓reduceIte, BitVec.toNat_add, BitVec.toNat_ofNat,
      (show (1 : BitVec 32).toNat = 1 from rfl), Leanux.WG.fls, beq_iff_eq, zero]
    omega

/-- The C helper returns u8. Its 128-bit path starts from 0xffffff80 in
    EBP, so the full EAX is deliberately not the source natural result. -/
theorem result_low8 (bits n : Nat) (family : bits = 32 ∨ bits = 128)
    (bounded : n ≤ bits) :
    ((BitVec.ofNat 32 bits - BitVec.ofNat 32 n).setWidth 8).toNat = bits - n := by
  have small : bits < 256 := by rcases family with rfl | rfl <;> decide
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem fls_le (x bits : Nat) (bound : x < 2^bits) : Leanux.WG.fls x ≤ bits := by
  by_cases zero : x = 0
  · simp [Leanux.WG.fls, zero]
  · have less := (Nat.log2_lt zero).mpr bound
    simp only [Leanux.WG.fls, beq_iff_eq, zero, ↓reduceIte]
    omega

/-- The compiler's signed-byte 128 constant has the same AL result. -/
theorem signed128_result (n : Nat) (bound : n ≤ 128) :
    ((0xffffff80#32 - BitVec.ofNat 32 n).setWidth 8).toNat = 128 - n := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_sub]
  change (((4294967296 - n % 4294967296) + 4294967168) % 4294967296) % 256 = 128 - n
  omega

theorem seededScan_word (x : Nat) (bound : x < 2^128) :
    seededScan x + 1 = BitVec.ofNat 32 (Leanux.WG.fls x) := by
  apply BitVec.eq_of_toNat_eq
  rw [seededScan_fls x bound, BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (by have h := fls_le x 128 bound; omega)).symm

theorem xor_high (stored query : Nat) :
    (stored ^^^ query) / 2^64 = (stored / 2^64) ^^^ (query / 2^64) :=
  Nat.xor_div_two_pow

theorem xor_low (stored query : Nat) :
    (stored ^^^ query) % 2^64 = (stored % 2^64) ^^^ (query % 2^64) :=
  Nat.xor_mod_two_pow

#print axioms seededScan_word
#print axioms signed128_result
#print axioms seededScan_fls
#print axioms result_low8
end Binary.CommonBits
