import AllowedipsNodeCopyChecked

/-! Result C1, work package 3: bit-vector facts for the internal node's
header computation. The prefix length reaches the header code in a 32-bit
register whose upper 24 bits are not known (`r13d` after `common_bits`
returns a byte in `al`); every use reads the low byte only. -/
namespace Binary.Pair.Allowedips.C1Internal

theorem low_byte_wide (x : BitVec 32) :
    BitVec.extractLsb' 0 8 (BitVec.setWidth 64 x)=x.setWidth 8 := by
  ext i hi
  simp
  omega

theorem low_byte_replace (y : BitVec 64) (b : BitVec 8) :
    BitVec.extractLsb' 0 8 (y.replaceLow b)=b := by
  ext i hi
  simp [BitVec.replaceLow,BitVec.drop]
  rw [BitVec.getLsbD_append]
  simp [hi]

theorem low32_wide (z : BitVec 32) : BitVec.extractLsb' 0 32 (BitVec.setWidth 64 z)=z := by
  ext i hi
  simp
  have wide : i<64 := by omega
  simp [wide,BitVec.getLsbD_eq_getElem hi]

theorem replace_replace (y : BitVec 64) (a b : BitVec 8) :
    (y.replaceLow a).replaceLow b=y.replaceLow b := by
  ext i hi
  simp only [BitVec.replaceLow,BitVec.drop,BitVec.getElem_setWidth,BitVec.append_eq]
  rw [BitVec.getLsbD_append,BitVec.getLsbD_append]
  by_cases small : i<8
  · simp [small]
  · simp [small]
    have back : 8+(i-8)=i := by omega
    rw [back,BitVec.getLsbD_append]
    simp [small,back]

theorem low_byte_byte (b : BitVec 8) : BitVec.extractLsb' 0 8 (BitVec.setWidth 64 b)=b := by
  ext i hi
  have wide : i<64 := by omega
  simp [wide,BitVec.getLsbD_eq_getElem hi]

theorem low_byte_word (y : BitVec 64) :
    BitVec.setWidth 8 (BitVec.extractLsb' 0 32 y)=BitVec.extractLsb' 0 8 y := by
  ext i hi
  have wide : i<32 := by omega
  simp [wide]

theorem low_byte_word_byte (b : BitVec 8) :
    BitVec.setWidth 8 (BitVec.extractLsb' 0 32 (BitVec.setWidth 64 b))=b := by
  rw [low_byte_word,low_byte_byte]

/-- `cmovbe` after `cmp %dil,%r13b`: taken exactly when the common length is
at most the requested one. -/
theorem below_finite : ∀ cidr common : Fin 129,
    ((¬BitVec.unsigned (BitVec.ofNat 8 common.val-BitVec.ofNat 8 cidr.val)=
        (BitVec.ofNat 8 common.val).unsigned-(BitVec.ofNat 8 cidr.val).unsigned ∨
      BitVec.ofNat 8 common.val-BitVec.ofNat 8 cidr.val=0#8) ↔ common.val≤cidr.val) := by
  decide +kernel

private theorem seven_bit : ∀ i : Fin 32, (7#32)[i.val]=decide (i.val<3) := by decide

theorem low_bits_not (y : BitVec 32) :
    ~~~y &&& 7#32=(~~~(y.setWidth 8)).setWidth 32 &&& 7#32 := by
  ext i hi
  have bit := seven_bit ⟨i,hi⟩
  simp only at bit
  simp [bit]
  by_cases small : i<3
  · have wide : i<8 := by omega
    simp [small,wide]
    exact (BitVec.getLsbD_eq_getElem hi).symm
  · simp [small]

private theorem seven_bit_wide : ∀ i : Fin 64, (7#64)[i.val]=decide (i.val<3) := by decide

theorem wide_and_seven (z : BitVec 32) : BitVec.setWidth 64 z &&& 7#64=BitVec.setWidth 64 (z &&& 7#32) := by
  ext i hi
  have bit := seven_bit_wide ⟨i,hi⟩
  simp only at bit
  by_cases small : i<3
  · have narrow : i<32 := by omega
    simp [bit,small,BitVec.getLsbD_eq_getElem narrow]
  · simp [bit,small]

private theorem not_low_finite : ∀ v : Fin 129,
    BitVec.setWidth 64 ((~~~BitVec.ofNat 8 v.val).setWidth 32 &&& 7#32)=BitVec.ofNat 64 (7-v.val%8) := by
  decide +kernel

/-- The bit selector `7 - cidr % 8` from a register whose low byte is the
prefix length. -/
theorem not_low3 (x : BitVec 32) (l : Nat) (low : x.setWidth 8=BitVec.ofNat 8 l) (bound : l≤128) :
    BitVec.setWidth 64 (~~~x) &&& 7#64=BitVec.ofNat 64 (7-l%8) := by
  rw [wide_and_seven,low_bits_not,low]
  exact not_low_finite ⟨l,by omega⟩

end Binary.Pair.Allowedips.C1Internal
