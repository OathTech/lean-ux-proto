import Kraken.Mem

namespace Binary

/-- Subtracting an aligned offset preserves word alignment, including wraparound. -/
theorem aligned_sub (address offset : UInt64)
    (aligned : address.toNat % 8 = 0) (offsetAligned : offset.toNat % 8 = 0) :
    (address - offset).toNat % 8 = 0 := by
  simp only [UInt64.toNat_sub]
  have addressBound := address.toNat_lt_size
  have offsetBound := offset.toNat_lt_size
  omega

end Binary
