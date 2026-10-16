import Leanux.Proofs.WG.AllowedIps.Prefix

/-!
# The mirror's prefix arithmetic

These execution equations retain the branch records, as well as the result
and the complete Ambient state. The width and address premises in the matching
theorem are the address-family invariants used by the trie representation.
-/

namespace Leanux.Proofs.WG.AllowedIps

open Leanux

/-- One branch record, with the same section marker as the mirror. -/
def record (w : Ambient) (d : Decision) (outcome : Bool) : Ambient :=
  { w with steps := w.steps.push { decision := d, outcome, netRx := w.netRxSection } }

/-- The complete bookkeeping of `commonBits`, including its unsupported-width
return of zero. The two supported families are selected by its callers. -/
def commonRecords (w : Ambient) (width x : Nat) : Ambient :=
  let w := record w .commonBits32 (width == 32)
  if width == 32 then w else
  let w := record w .commonBits128 (width == 128)
  if width == 128 then record w .fls128High (x / 2 ^ 64 != 0) else w

/-- The arithmetic returned by the mirror before normalizing its IPv6 split. -/
def commonValue (width a b : Nat) : Nat :=
  if width == 32 then 32 - WG.fls (a ^^^ b) else
  if width == 128 then
    let x := a ^^^ b
    128 - (if x / 2 ^ 64 != 0 then WG.fls (x / 2 ^ 64) + 64
      else WG.fls (x % 2 ^ 64))
  else 0

/-- Exact execution of the original highest-set-bit helper, for every width. -/
theorem commonBits_run_raw (n : WG.AipNode) (key width : Nat) (w : Ambient) :
    (WG.commonBits (m := AmbientM) n key width).run w =
      .ok (commonValue width n.bits key, commonRecords w width (n.bits ^^^ key)) := by
  by_cases h32 : width = 32
  · subst width
    rfl
  · by_cases h128 : width = 128
    · subst width
      by_cases hh : (n.bits ^^^ key) / 2 ^ 64 = 0
      · simp [WG.commonBits, branch, AmbientM.branch, commonValue, commonRecords, record, hh] <;> rfl
      · simp [WG.commonBits, branch, AmbientM.branch, commonValue, commonRecords, record, hh] <;> rfl
    · simp [WG.commonBits, branch, AmbientM.branch, commonValue, commonRecords, record, h32, h128] <;> rfl

theorem commonValue_supported (width a b : Nat) (hw : width = 32 ∨ width = 128) :
    commonValue width a b = common width a b := by
  rcases hw with rfl | rfl
  · rfl
  · change (128 - (if (a ^^^ b) / 2 ^ 64 != 0 then WG.fls ((a ^^^ b) / 2 ^ 64) + 64
        else WG.fls ((a ^^^ b) % 2 ^ 64))) = 128 - WG.fls (a ^^^ b)
    rw [split_fls]

/-- Both supported address families compute the same width-parametric
common-prefix function, with exactly the mirror's branch records. -/
theorem commonBits_run (n : WG.AipNode) (key width : Nat) (w : Ambient)
    (hw : width = 32 ∨ width = 128) :
    (WG.commonBits (m := AmbientM) n key width).run w =
      .ok (common width n.bits key, commonRecords w width (n.bits ^^^ key)) := by
  rw [commonBits_run_raw, commonValue_supported width n.bits key hw]

/-- Exact execution of the original prefix test before its arithmetic
result is expressed as equality of leading address bits. -/
theorem prefixMatches_run_value (n : WG.AipNode) (key width : Nat) (w : Ambient)
    (hw : width = 32 ∨ width = 128) :
    (WG.prefixMatches (m := AmbientM) n key width).run w =
      .ok (decide (n.cidr ≤ common width n.bits key),
        commonRecords w width (n.bits ^^^ key)) := by
  change ((WG.commonBits (m := AmbientM) n key width).run w >>= fun out =>
    .ok (decide (n.cidr ≤ out.1), out.2)) = _
  rw [commonBits_run n key width w hw]
  rfl

/-- On bounded addresses of either family, the original prefix test returns
true exactly when the addresses share the node's leading prefix bits. -/
theorem prefixMatches_run (n : WG.AipNode) (key width : Nat) (w : Ambient)
    (hw : width = 32 ∨ width = 128) (hn : n.bits < 2 ^ width)
    (hk : key < 2 ^ width) (hc : n.cidr ≤ width) :
    (WG.prefixMatches (m := AmbientM) n key width).run w =
      .ok (decide (prefixBits width n.cidr n.bits = prefixBits width n.cidr key),
        commonRecords w width (n.bits ^^^ key)) := by
  rw [prefixMatches_run_value n key width w hw]
  simp only [common_ge_iff hn hk hc]

/-- The original branch selector returns the next address bit without an
effect when the node's prefix is shorter than its address width, in every
monad admitted by the actual function. -/
theorem choose_run {m : Type → Type} [Monad m] [MonadLiftT AmbientM m]
    (n : WG.AipNode) (key : Nat) (hc : n.cidr < n.bitlen) :
    (WG.choose n key : m Nat) = pure (bit n.bitlen n.cidr key) := by
  have h : ¬ n.cidr ≥ n.bitlen := by omega
  simp [WG.choose, h, bit] <;> rfl

end Leanux.Proofs.WG.AllowedIps
