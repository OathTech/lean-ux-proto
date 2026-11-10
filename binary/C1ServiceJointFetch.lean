import C1ServiceCallbackText
import AllowedipsMutationImage
import StatementC1CallbackImage
import TrustBase

/-! One decoder for everything result C1 names: the shared service bodies,
the two comparison entries of `StatementC1CallbackImage`, a stub at the two
service addresses, the lookup image (`lookup`'s index image and
`wg_peer_get_maybe_zero`), the allowed-IPs image (`lookup`, `common_bits`),
`add.isra.0` and both insertion wrappers. The decoder agreements the landed
results take as premises had not been met jointly by one `fetch` (review
finding N4): here each listing is shown to lie in its own address interval,
the intervals are apart, and so each agreement holds of the union.

This module depends on the committed image terms only. -/
namespace Binary.Statements.C1.Joint
open Binary.Callback.Text

/-- Every decoded address of `f` lies in `[low, high]`. -/
def Within (f : Int64 → Option Decoded) (low high : Nat) : Prop :=
  ∀ pc decoded, f pc = some decoded → low ≤ pc.toBitVec.toNat ∧ pc.toBitVec.toNat ≤ high

theorem Within.none {f : Int64 → Option Decoded} {low high : Nat} (within : Within f low high)
    {pc : Int64} (outside : pc.toBitVec.toNat < low ∨ high < pc.toBitVec.toNat) : f pc = none := by
  cases here : f pc with
  | none => rfl
  | some decoded =>
    have := within pc decoded here
    omega

/-! ## The intervals -/

theorem service_within : Within ServiceImage.fetch 18446744071579316928 18446744071579844877 := by
  intro pc decoded here
  have rows : ServiceImage.decoded.all
      (fun row => 18446744071579316928 ≤ row.1 && row.1 ≤ 18446744071579844877) = true := by
    decide +kernel
  unfold ServiceImage.fetch at here
  cases found : ServiceImage.decoded.find? (fun row => row.1 == pc.toUInt64.toNat) with
  | none => simp [found] at here
  | some row =>
    have bound := List.all_eq_true.mp rows row (List.mem_of_find?_eq_some found)
    have same := List.find?_some found
    simp only [beq_iff_eq] at same
    simp only [Bool.and_eq_true, decide_eq_true_eq] at bound
    have view : pc.toUInt64.toNat = pc.toBitVec.toNat := rfl
    omega

/-- The ten addresses of the two comparison entries. -/
theorem entries_listed {pc : Int64} {decoded : Decoded}
    (here : StatementC1CallbackImage.fetch pc = some decoded) :
    ∃ row ∈ StatementC1CallbackImage.decoded, row.1 = pc.toUInt64.toNat := by
  unfold StatementC1CallbackImage.fetch at here
  cases found : StatementC1CallbackImage.decoded.find? (fun row => row.1 == pc.toUInt64.toNat) with
  | none => simp [found] at here
  | some row =>
    have same := List.find?_some found
    simp only [beq_iff_eq] at same
    exact ⟨row,List.mem_of_find?_eq_some found,same⟩

theorem entries_within :
    Within StatementC1CallbackImage.fetch 18446744071579844672 18446744071579844783 := by
  intro pc decoded here
  obtain ⟨row,member,same⟩ := entries_listed here
  have rows : StatementC1CallbackImage.decoded.all
      (fun row => 18446744071579844672 ≤ row.1 && row.1 ≤ 18446744071579844783) = true := by
    decide +kernel
  have bound := List.all_eq_true.mp rows row member
  simp only [Bool.and_eq_true, decide_eq_true_eq] at bound
  have view : pc.toUInt64.toNat = pc.toBitVec.toNat := rfl
  omega

/-- The shared service bodies hold nothing at the two comparison entries. -/
theorem service_none_at_entries {pc : Int64} {decoded : Decoded}
    (here : StatementC1CallbackImage.fetch pc = some decoded) : ServiceImage.fetch pc = none := by
  obtain ⟨row,member,same⟩ := entries_listed here
  have rows : StatementC1CallbackImage.decoded.all (fun row =>
      (ServiceImage.decoded.find? (fun other => other.1 == row.1)).isNone) = true := by
    decide +kernel
  have absent := List.all_eq_true.mp rows row member
  unfold ServiceImage.fetch
  rw [← same]
  rw [Option.isNone_iff_eq_none] at absent
  simp [absent]

theorem anchored_within : Within Image.fetch 18446744071582619664 18446744071582648655 := by
  intro pc decoded here
  unfold Image.fetch at here
  cases lookup : Image.fetchIn Image.Lookup.entry Image.Lookup.code pc with
  | some found =>
    have range := fetchIn_address lookup (by decide +kernel)
    have low : 18446744071582619664 ≤ Image.Lookup.entry.toBitVec.toNat := by decide +kernel
    have high : Image.Lookup.entry.toBitVec.toNat + extent Image.Lookup.code ≤ 18446744071582648655 := by
      decide +kernel
    omega
  | none =>
    rw [lookup] at here
    have range := fetchIn_address (show Image.fetchIn Image.PeerGet.entry Image.PeerGet.code pc =
      some decoded from here) (by decide +kernel)
    have low : 18446744071582619664 ≤ Image.PeerGet.entry.toBitVec.toNat := by decide +kernel
    have high : Image.PeerGet.entry.toBitVec.toNat + extent Image.PeerGet.code ≤ 18446744071582648655 := by
      decide +kernel
    omega

theorem allowedips_within : Within AllowedipsImage.fetch 18446744071582648656 18446744071582649279 := by
  intro pc decoded here
  refine ⟨allowedips_low here,?_⟩
  unfold AllowedipsImage.fetch at here
  cases lookup : Image.fetchIn AllowedipsImage.Lookup.entry AllowedipsImage.Lookup.code pc with
  | some found =>
    have range := fetchIn_address lookup (by decide +kernel)
    have high : AllowedipsImage.Lookup.entry.toBitVec.toNat + extent AllowedipsImage.Lookup.code ≤
        18446744071582649279 := by decide +kernel
    omega
  | none =>
    rw [lookup] at here
    have range := fetchIn_address (show Image.fetchIn AllowedipsImage.CommonBits.entry
      AllowedipsImage.CommonBits.code pc = some decoded from here) (by decide +kernel)
    have high : AllowedipsImage.CommonBits.entry.toBitVec.toNat +
        extent AllowedipsImage.CommonBits.code ≤ 18446744071582649279 := by decide +kernel
    omega

/-- A decoder result at `pc` is absent or inside `[low, high]`. -/
def Bounded (pc : Int64) (low high : Nat) (result : Option Decoded) : Prop :=
  ∀ decoded, result = some decoded → low ≤ pc.toBitVec.toNat ∧ pc.toBitVec.toNat ≤ high

/-- One branch of a generated decoder tree. -/
theorem Bounded.ite {pc : Int64} {low high : Nat} {condition : Prop} [Decidable condition]
    {left right : Option Decoded} (first : Bounded pc low high left)
    (second : Bounded pc low high right) :
    Bounded pc low high (if condition then left else right) := by
  split
  · exact first
  · exact second

/-- One leaf of a generated decoder tree: a listing segment inside `[low, high]`. -/
theorem Bounded.segment {entry : Int64} {code : List (Kraken.Sized Directive)} {pc : Int64}
    {low high : Nat} (fits : entry.toBitVec.toNat + extent code < 2^64)
    (lower : low ≤ entry.toBitVec.toNat) (upper : entry.toBitVec.toNat + extent code ≤ high) :
    Bounded pc low high (Image.fetchIn entry code pc) := by
  intro decoded here
  have range := fetchIn_address here fits
  omega

theorem insert4_within :
    Within AllowedipsMutationImage.Insert4.fetch 18446744071582651440 18446744071582651519 := by
  intro pc
  change Bounded pc _ _ _
  unfold AllowedipsMutationImage.Insert4.fetch
  repeat' first | (apply Bounded.segment <;> decide +kernel) | apply Bounded.ite

theorem insert6_within :
    Within AllowedipsMutationImage.Insert6.fetch 18446744071582651520 18446744071582651615 := by
  intro pc
  change Bounded pc _ _ _
  unfold AllowedipsMutationImage.Insert6.fetch
  repeat' first | (apply Bounded.segment <;> decide +kernel) | apply Bounded.ite

theorem add_within :
    Within AllowedipsMutationImage.Add.fetch 18446744071582649280 18446744071582651439 := by
  intro pc
  change Bounded pc _ _ _
  unfold AllowedipsMutationImage.Add.fetch
  repeat' first | (apply Bounded.segment <;> decide +kernel) | apply Bounded.ite

/-! ## The union -/

/-- The interval reserved for the stub at the two service addresses
(`allocEntry` 0xffffffff81196d20, `freeEntry` 0xffffffff81199b10). -/
def stubLow : Nat := 18446744071580511520
def stubHigh : Nat := 18446744071580523535

/-- The common decoder, for any stub code in the stub's interval. -/
def fetch (stub : Int64 → Option Decoded) (pc : Int64) : Option Decoded :=
  (ServiceImage.fetch pc).orElse fun _ =>
  (StatementC1CallbackImage.fetch pc).orElse fun _ =>
  (stub pc).orElse fun _ =>
  (Image.fetch pc).orElse fun _ =>
  (AllowedipsImage.fetch pc).orElse fun _ =>
  (AllowedipsMutationImage.Add.fetch pc).orElse fun _ =>
  (AllowedipsMutationImage.Insert4.fetch pc).orElse fun _ =>
  AllowedipsMutationImage.Insert6.fetch pc

variable {stub : Int64 → Option Decoded}

theorem services_agree : TrustBase.ServiceDecoderAgreement (fetch stub) := by
  intro pc decoded here
  simp [fetch, here]

theorem entries_agree (pc : Int64) (decoded : Decoded)
    (here : StatementC1CallbackImage.fetch pc = some decoded) : fetch stub pc = some decoded := by
  simp [fetch, service_none_at_entries here, here]

theorem stub_agrees (within : Within stub stubLow stubHigh) (pc : Int64) (decoded : Decoded)
    (here : stub pc = some decoded) : fetch stub pc = some decoded := by
  have range := within pc decoded here
  simp only [stubLow, stubHigh] at range
  simp [fetch, service_within.none (pc := pc) (by omega), entries_within.none (pc := pc) (by omega), here]

theorem anchored_agrees (within : Within stub stubLow stubHigh) :
    TrustBase.AnchoredDecoderAgreement (fetch stub) := by
  intro pc decoded here
  have range := anchored_within pc decoded here
  simp [fetch, service_within.none (pc := pc) (by omega), entries_within.none (pc := pc) (by omega),
    within.none (pc := pc) (by simp only [stubLow, stubHigh]; omega), here]

theorem allowedips_agrees (within : Within stub stubLow stubHigh) :
    TrustBase.AllowedipsDecoderAgreement (fetch stub) := by
  intro pc decoded here
  have range := allowedips_within pc decoded here
  simp [fetch, service_within.none (pc := pc) (by omega), entries_within.none (pc := pc) (by omega),
    within.none (pc := pc) (by simp only [stubLow, stubHigh]; omega),
    anchored_within.none (pc := pc) (by omega), here]

theorem mutation_agrees (within : Within stub stubLow stubHigh) :
    TrustBase.AllowedipsMutationDecoderAgreement (fetch stub) := by
  refine ⟨?_,?_,?_⟩
  · intro pc decoded here
    have range := insert4_within pc decoded here
    simp [fetch, service_within.none (pc := pc) (by omega), entries_within.none (pc := pc) (by omega),
      within.none (pc := pc) (by simp only [stubLow, stubHigh]; omega),
      anchored_within.none (pc := pc) (by omega), allowedips_within.none (pc := pc) (by omega),
      add_within.none (pc := pc) (by omega), here]
  · intro pc decoded here
    have range := insert6_within pc decoded here
    simp [fetch, service_within.none (pc := pc) (by omega), entries_within.none (pc := pc) (by omega),
      within.none (pc := pc) (by simp only [stubLow, stubHigh]; omega),
      anchored_within.none (pc := pc) (by omega), allowedips_within.none (pc := pc) (by omega),
      add_within.none (pc := pc) (by omega), insert4_within.none (pc := pc) (by omega), here]
  · intro pc decoded here
    have range := add_within pc decoded here
    simp [fetch, service_within.none (pc := pc) (by omega), entries_within.none (pc := pc) (by omega),
      within.none (pc := pc) (by simp only [stubLow, stubHigh]; omega),
      anchored_within.none (pc := pc) (by omega), allowedips_within.none (pc := pc) (by omega), here]

#print axioms mutation_agrees
#print axioms allowedips_agrees
#print axioms anchored_agrees
#print axioms entries_agree
end Binary.Statements.C1.Joint
