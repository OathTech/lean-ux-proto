import CallbackGuarded
import CallbackAgreement
import AllowedipsImage
import ServiceImage

/-! Where the callbacks' text lies. The contracts of the allowed-IPs results
(`TrustBase.AllowedipsServiceReturns`) ask that no state inside a callback is
at an instruction of `AllowedipsImage`; the landed leaf proofs only keep the
interior out of the lookup image. Here: a decoded instruction of a listing
lies within the listing's byte length of its entry, the shared service bodies
lie below the allowed-IPs image, and a guarded execution over
`ServiceImage.fetch` stays in `ServiceImage`'s text.

This module depends on landed modules only (nothing of result C1). -/
namespace Binary.Callback.Text
open TrustBase
local instance : Labels := Image.linkedLabels

/-- The byte length of a listing. -/
def extent (code : List (Kraken.Sized Directive)) : Nat := (code.map (·.size)).sum

/-- A decoded instruction of a listing starts within the listing. -/
theorem fetchIn_within {entry : Int64} {code : List (Kraken.Sized Directive)} {target : Int64}
    {decoded : Decoded} (here : Image.fetchIn entry code target = some decoded) :
    ∃ offset ≤ extent code, target.toBitVec = entry.toBitVec + .ofNat 64 offset := by
  induction code generalizing entry with
  | nil => simp [Image.fetchIn] at here
  | cons head rest ih =>
    obtain ⟨directive,size⟩ := head
    unfold Image.fetchIn at here
    split at here
    · rename_i same
      exact ⟨0,Nat.zero_le _,by simp [same]⟩
    · obtain ⟨offset,bound,at_⟩ := ih here
      refine ⟨size+offset,by simp only [extent, List.map_cons, List.sum_cons] at bound ⊢; omega,?_⟩
      have literal : (Int64.ofNat size).toBitVec = BitVec.ofNat 64 size := rfl
      rw [at_, Int64.toBitVec_add, literal, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The address of a decoded instruction as a natural number, when the listing
does not wrap. -/
theorem fetchIn_address {entry : Int64} {code : List (Kraken.Sized Directive)} {target : Int64}
    {decoded : Decoded} (here : Image.fetchIn entry code target = some decoded)
    (fits : entry.toBitVec.toNat + extent code < 2^64) :
    entry.toBitVec.toNat ≤ target.toBitVec.toNat ∧
      target.toBitVec.toNat ≤ entry.toBitVec.toNat + extent code := by
  obtain ⟨offset,bound,at_⟩ := fetchIn_within here
  rw [at_, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The lowest address of the allowed-IPs image (`common_bits`). -/
def allowedipsLow : Nat := 18446744071582648656

theorem allowedips_low {pc : Int64} {decoded : Decoded}
    (here : AllowedipsImage.fetch pc = some decoded) : allowedipsLow ≤ pc.toBitVec.toNat := by
  unfold AllowedipsImage.fetch at here
  cases lookup : Image.fetchIn AllowedipsImage.Lookup.entry AllowedipsImage.Lookup.code pc with
  | some found =>
    have range := (fetchIn_address lookup (by decide +kernel)).1
    have entry : AllowedipsImage.Lookup.entry.toBitVec.toNat = 18446744071582648880 := by decide +kernel
    simp only [allowedipsLow]
    omega
  | none =>
    rw [lookup] at here
    have range := (fetchIn_address (show Image.fetchIn AllowedipsImage.CommonBits.entry
      AllowedipsImage.CommonBits.code pc = some decoded from here) (by decide +kernel)).1
    have entry : AllowedipsImage.CommonBits.entry.toBitVec.toNat = 18446744071582648656 := by decide +kernel
    simp only [allowedipsLow]
    omega

/-- Every instruction of the shared service bodies lies below the allowed-IPs image. -/
theorem service_below {pc : Int64} (here : (ServiceImage.fetch pc).isSome = true) :
    pc.toBitVec.toNat < allowedipsLow := by
  have rows : ServiceImage.decoded.all (fun row => row.1 < allowedipsLow) = true := by decide +kernel
  unfold ServiceImage.fetch at here
  cases found : ServiceImage.decoded.find? (fun row => row.1 == pc.toUInt64.toNat) with
  | none => simp [found] at here
  | some row =>
    have member := List.mem_of_find?_eq_some found
    have same := List.find?_some found
    have bound := List.all_eq_true.mp rows row member
    simp only [beq_iff_eq] at same
    simp only [decide_eq_true_eq] at bound
    have view : pc.toUInt64.toNat = pc.toBitVec.toNat := rfl
    omega

/-- No instruction of the shared service bodies is one of the allowed-IPs image. -/
theorem service_apart {pc : Int64} (here : (ServiceImage.fetch pc).isSome = true) :
    AllowedipsImage.fetch pc = none := by
  cases other : AllowedipsImage.fetch pc with
  | none => rfl
  | some decoded =>
    have := allowedips_low other
    have := service_below here
    omega

/-- A guarded execution over the service image only ever executes the service
image's instructions: the guard may be strengthened by that. -/
theorem in_service {guard P : MachineState → Prop} {s : MachineState}
    (run : Eventually (guardedStep ServiceImage.fetch guard) P s) :
    Eventually (guardedStep ServiceImage.fetch
      (fun q => guard q ∧ (ServiceImage.fetch q.pc).isSome = true)) P s := by
  induction run with
  | done s hp => exact .done s hp
  | step s mid step _ ih =>
    apply step_cps
    refine ⟨⟨step.1,?_⟩,instruction_mono ServiceImage.fetch s _ _ ih step.2⟩
    have fetched := step.2
    unfold instructionStep at fetched
    cases read : ServiceImage.fetch s.pc with
    | none => simp [read] at fetched
    | some decoded => rfl

#print axioms service_apart
#print axioms in_service
end Binary.Callback.Text
