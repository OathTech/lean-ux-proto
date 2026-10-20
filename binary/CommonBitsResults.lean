import CommonBitsRegions
import CommonBitsArithmetic

namespace Binary.CommonBits

private theorem word_zero {n : Nat} (x : BitVec n) : x.toNat = 0 ↔ x = 0#n := by
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    simpa using h
  · intro h
    simp [h]

/-- The two machine scan widths have the same seeded low-word interpretation. -/
theorem scan32_seed (x : BitVec 32) : scan32 x = seededScan x.toNat := by
  simp [scan32, seededScan, word_zero]

theorem scan64_seed (x : BitVec 64) : (scan64 x).setWidth 32 = seededScan x.toNat := by
  by_cases zero : x = 0#64
  · simp [zero, scan64, seededScan]
  · simp [scan64, seededScan, zero, word_zero]

theorem scan32_fls (x : BitVec 32) : scan32 x + 1 = .ofNat 32 (Leanux.WG.fls x.toNat) := by
  rw [scan32_seed]
  apply seededScan_word
  have bound := x.isLt
  change x.toNat < 2^32 at bound
  omega

theorem scan64_fls (x : BitVec 64) :
    (scan64 x).setWidth 32 + 1 = .ofNat 32 (Leanux.WG.fls x.toNat) := by
  rw [scan64_seed]
  apply seededScan_word
  have bound := x.isLt
  change x.toNat < 2^64 at bound
  omega

/-- IPv4's low result byte is the mirror's natural subtraction, including x=0. -/
theorem ipv4_result (x : BitVec 32) :
    ((32#32 - (scan32 x + 1)).setWidth 8).toNat = 32 - Leanux.WG.fls x.toNat := by
  rw [scan32_fls]
  exact result_low8 32 _ (Or.inl rfl) (fls_le _ 32 x.isLt)

/-- Only DL is a C argument: arbitrary upper EDX bits do not affect AL. -/
theorem ipv4_result_of_byte (bits : BitVec 32) (family : bits.setWidth 8 = 32#8)
    (x : BitVec 32) :
    ((bits - (scan32 x + 1)).setWidth 8).toNat = 32 - Leanux.WG.fls x.toNat := by
  have low : (bits - (scan32 x+1)).setWidth 8 = (32#32 - (scan32 x+1)).setWidth 8 := by
    have familyNat := congrArg BitVec.toNat family
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at familyNat
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
    have a := bits.isLt
    have b := (scan32 x+1).isLt
    omega
  rw [low]
  exact ipv4_result x

/-- The low-word IPv6 path preserves the equality case: fls(0)=0 yields 128. -/
theorem ipv6_low_result (x : BitVec 64) :
    ((0xffffff80#32 - ((scan64 x).setWidth 32 + 1)).setWidth 8).toNat =
      128 - Leanux.WG.fls x.toNat := by
  rw [scan64_fls]
  apply signed128_result
  have bound := fls_le _ 64 x.isLt
  omega

/-- Adding 0x41 to the seeded scan is fls(high)+64 in the high-word path. -/
theorem scan64_high_fls (x : BitVec 64) :
    (scan64 x).setWidth 32 + 65 = .ofNat 32 (Leanux.WG.fls x.toNat + 64) := by
  rw [show (65 : BitVec 32) = 1 + 64 from rfl, ← BitVec.add_assoc, scan64_fls,
    BitVec.ofNat_add]
  rfl

theorem ipv6_high_result (x : BitVec 64) :
    ((0xffffff80#32 - ((scan64 x).setWidth 32 + 65)).setWidth 8).toNat =
      128 - (Leanux.WG.fls x.toNat + 64) := by
  rw [scan64_high_fls]
  apply signed128_result
  have bound := fls_le _ 64 x.isLt
  omega

end Binary.CommonBits
