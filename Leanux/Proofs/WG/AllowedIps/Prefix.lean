import Leanux.WG.AllowedIps
import Init.Data.Nat.Bitwise.Lemmas
import Init.Data.Nat.Div.Lemmas

/-!
# Arithmetic of the allowed-IP trie

The mirror stores an unmasked address. A prefix is its leading `cidr` bits,
and a branch examines the following bit. The arithmetic below is uniform in
the address width; only the mirror's operational entry points distinguish
IPv4 from IPv6.
-/

namespace Leanux.Proofs.WG.AllowedIps

open Leanux.WG

/-- The leading `cidr` bits of an address with the stated width. -/
def prefixBits (width cidr addr : Nat) : Nat :=
  addr / 2 ^ (width - cidr)

/-- The bit immediately after the prefix, in the mirror's integer encoding. -/
def bit (width cidr addr : Nat) : Nat :=
  addr / 2 ^ (width - 1 - cidr) % 2

/-- The length of the common leading prefix of two bounded addresses. -/
def common (width a b : Nat) : Nat :=
  width - fls (a ^^^ b)

theorem fls_le_iff (x k : Nat) : fls x ≤ k ↔ x < 2 ^ k := by
  by_cases hx : x = 0
  · subst x
    constructor
    · intro _
      exact Nat.two_pow_pos k
    · intro _
      simp [fls]
  · simpa [fls, hx, Nat.add_one_le_iff] using (Nat.log2_lt (k := k) hx)

theorem lt_pow_fls (x : Nat) : x < 2 ^ fls x :=
  (fls_le_iff x _).mp (Nat.le_refl _)

/-- When the high part is nonzero, its highest set bit determines the
highest set bit of the whole integer. -/
theorem fls_div_pow (x k : Nat) (h : x / 2 ^ k ≠ 0) :
    fls x = fls (x / 2 ^ k) + k := by
  have hupper : fls x ≤ fls (x / 2 ^ k) + k := by
    apply (fls_le_iff _ _).mpr
    rw [Nat.pow_add]
    exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)).mp (lt_pow_fls _)
  have hxlo : 2 ^ k ≤ x := (Nat.div_ne_zero_iff.mp h).2
  have hn : ¬ fls x ≤ k := fun hf =>
    (Nat.not_lt_of_ge hxlo) ((fls_le_iff x k).mp hf)
  have hk : k ≤ fls x := by omega
  have hp : 2 ^ (fls x - k) * 2 ^ k = 2 ^ fls x := by
    rw [← Nat.pow_add, Nat.sub_add_cancel hk]
  have hquot : x / 2 ^ k < 2 ^ (fls x - k) := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)).mpr
    rw [hp]
    exact lt_pow_fls x
  have hlower := (fls_le_iff _ _).mpr hquot
  omega

/-- The high/low calculation used by `commonBits` for IPv6 computes the
same highest-set-bit position as the unsplit integer. -/
theorem split_fls (x k : Nat) :
    (if x / 2 ^ k != 0 then fls (x / 2 ^ k) + k else fls (x % 2 ^ k)) =
      fls x := by
  by_cases h : x / 2 ^ k = 0
  · have hx : x < 2 ^ k := (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos k)).mp h
    simp [h, Nat.mod_eq_of_lt hx]
  · simpa [h] using (fls_div_pow x k h).symm

theorem xor_eq_zero_iff (a b : Nat) : a ^^^ b = 0 ↔ a = b := by
  constructor
  · intro h
    have := congrArg (fun z => z ^^^ b) h
    simpa [Nat.xor_assoc] using this
  · rintro rfl
    simp

theorem common_le (width a b : Nat) : common width a b ≤ width := by
  unfold common
  omega

@[simp] theorem common_self (width a : Nat) : common width a a = width := by
  simp [common, fls]

theorem common_symm (width a b : Nat) : common width a b = common width b a := by
  rw [common, common, Nat.xor_comm]

@[simp] theorem prefix_full (width a : Nat) : prefixBits width width a = a := by
  simp [prefixBits]

theorem prefix_zero {width a : Nat} (ha : a < 2 ^ width) : prefixBits width 0 a = 0 := by
  simpa [prefixBits] using Nat.div_eq_of_lt ha

theorem prefix_lt {width cidr a : Nat} (hc : cidr ≤ width) (ha : a < 2 ^ width) :
    prefixBits width cidr a < 2 ^ cidr := by
  unfold prefixBits
  apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
  rw [← Nat.pow_add, show cidr + (width - cidr) = width by omega]
  exact ha

theorem prefix_div {width c d a : Nat} (hcd : c ≤ d) (hd : d ≤ width) :
    prefixBits width c a = prefixBits width d a / 2 ^ (d - c) := by
  unfold prefixBits
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  rw [show width - d + (d - c) = width - c by omega]

theorem prefix_eq_of_le {width c d a b : Nat} (hcd : c ≤ d) (hd : d ≤ width)
    (h : prefixBits width d a = prefixBits width d b) :
    prefixBits width c a = prefixBits width c b := by
  rw [prefix_div (a := a) hcd hd, prefix_div (a := b) hcd hd, h]

theorem bit_lt_two (width cidr addr : Nat) : bit width cidr addr < 2 := by
  exact Nat.mod_lt _ (by decide)

theorem bit_eq_prefix_succ (width c a : Nat) :
    bit width c a = prefixBits width (c + 1) a % 2 := by
  unfold bit prefixBits
  rw [show width - 1 - c = width - (c + 1) by omega]

theorem prefix_succ_div {width c a : Nat} (hc : c < width) :
    prefixBits width c a = prefixBits width (c + 1) a / 2 := by
  simpa using prefix_div (a := a) (c := c) (d := c + 1) (by omega) (by omega)

/-- One more matching prefix bit is exactly a matching shorter prefix and
a matching branch choice. -/
theorem prefix_succ_eq_iff {width c a b : Nat} (hc : c < width) :
    prefixBits width (c + 1) a = prefixBits width (c + 1) b ↔
      prefixBits width c a = prefixBits width c b ∧ bit width c a = bit width c b := by
  constructor
  · intro h
    constructor
    · exact prefix_eq_of_le (by omega) (by omega) h
    · simpa only [bit_eq_prefix_succ] using congrArg (fun n => n % 2) h
  · rintro ⟨hq, hr⟩
    rw [prefix_succ_div (a := a) hc, prefix_succ_div (a := b) hc] at hq
    simp only [bit_eq_prefix_succ] at hr
    have ha := Nat.div_add_mod (prefixBits width (c + 1) a) 2
    have hb := Nat.div_add_mod (prefixBits width (c + 1) b) 2
    omega

theorem bit_eq_of_prefix_eq {width c d a b : Nat} (hcd : c < d) (hd : d ≤ width)
    (h : prefixBits width d a = prefixBits width d b) : bit width c a = bit width c b := by
  have hs := prefix_eq_of_le (c := c + 1) (by omega) hd h
  exact ((prefix_succ_eq_iff (by omega)).mp hs).2

/-- The mirror's highest-set-bit test is equality of the requested
leading address bits, including the zero-length prefix. -/
theorem common_ge_iff {width cidr a b : Nat}
    (ha : a < 2 ^ width) (hb : b < 2 ^ width) (hc : cidr ≤ width) :
    cidr ≤ common width a b ↔ prefixBits width cidr a = prefixBits width cidr b := by
  have hf : fls (a ^^^ b) ≤ width :=
    (fls_le_iff _ _).mpr (Nat.xor_lt_two_pow ha hb)
  unfold common prefixBits
  calc
    cidr ≤ width - fls (a ^^^ b) ↔ fls (a ^^^ b) ≤ width - cidr := by omega
    _ ↔ a ^^^ b < 2 ^ (width - cidr) := fls_le_iff _ _
    _ ↔ (a ^^^ b) / 2 ^ (width - cidr) = 0 :=
      (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)).symm
    _ ↔ a / 2 ^ (width - cidr) = b / 2 ^ (width - cidr) := by
      rw [Nat.xor_div_two_pow, xor_eq_zero_iff]

theorem prefix_common {width a b : Nat} (ha : a < 2 ^ width) (hb : b < 2 ^ width) :
    prefixBits width (common width a b) a = prefixBits width (common width a b) b :=
  (common_ge_iff ha hb (common_le _ _ _)).mp (Nat.le_refl _)

theorem common_lt_of_ne {width a b : Nat}
    (ha : a < 2 ^ width) (hb : b < 2 ^ width) (hne : a ≠ b) :
    common width a b < width := by
  by_cases h : common width a b < width
  · exact h
  · have he := (common_ge_iff ha hb (Nat.le_refl width)).mp (by omega)
    exact False.elim (hne (by simpa using he))

/-- Distinct addresses split into opposite children immediately after
their maximal common prefix. -/
theorem common_split {width a b : Nat}
    (ha : a < 2 ^ width) (hb : b < 2 ^ width) (hne : a ≠ b) :
    common width a b < width ∧
      prefixBits width (common width a b) a = prefixBits width (common width a b) b ∧
      bit width (common width a b) a ≠ bit width (common width a b) b := by
  have hc := common_lt_of_ne ha hb hne
  have hp := prefix_common ha hb
  refine ⟨hc, hp, ?_⟩
  intro hbit
  have hs := (prefix_succ_eq_iff hc).mpr ⟨hp, hbit⟩
  have hle := (common_ge_iff ha hb (by omega)).mpr hs
  omega

theorem common_eq_of_match_and_bit_ne {width c a b : Nat}
    (ha : a < 2 ^ width) (hb : b < 2 ^ width) (hc : c < width)
    (hp : prefixBits width c a = prefixBits width c b) (hbit : bit width c a ≠ bit width c b) :
    common width a b = c := by
  have hlow := (common_ge_iff ha hb (by omega)).mpr hp
  have hhigh : ¬ c + 1 ≤ common width a b := by
    intro h
    have hs := (common_ge_iff ha hb (by omega)).mp h
    exact hbit ((prefix_succ_eq_iff hc).mp hs).2
  omega

end Leanux.Proofs.WG.AllowedIps
