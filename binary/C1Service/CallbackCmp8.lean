import C1Service.CallbackText
import C1Service.CallbackCmp8Rule
import StatementC1CallbackImage

/-! `__sanitizer_cov_trace_cmp8` for the allowed-IPs results, FROM the shared
rule `Binary.Callback.Cmp8.Cmp8Rule` (stated once for results C1 and C2 on
branch `task/binary-c2`, commit a6de3eed, and proved there by C2's work
package 1). Nothing is executed here: this module supplies the rule's
agreement premise from C1's image terms and shows that the callbacks' text is
apart from the allowed-IPs image, which the rule leaves to its user.

`C1Service.CallbackCmp8Image` and `C1Service.CallbackCmp8Rule` are the two
shared files of a6de3eed; the second differs from the original in its import
line only (lake builds a module only under a registered root's name). At
integration they are replaced by the originals and the two imports here
repointed. -/
namespace Binary.Callback.Cmp8
open TrustBase
local instance : Labels := Image.linkedLabels

/-- C1's image terms give the premise of `Cmp8Rule` (the adapter of
`binary/packets/c2/proof/C1-ADAPTER.md` on the C2 branch). -/
theorem c1_agreement (fetch : Int64 → Option Decoded)
    (reading : ∀ pc i, StatementC1CallbackImage.fetch pc = some i → fetch pc = some i) :
    Cmp8Agreement fetch := by
  intro pc i here
  apply reading
  by_cases h0 : pc = .ofNat 18446744071579844768
  · subst h0; exact here
  by_cases h1 : pc = .ofNat 18446744071579844772
  · subst h1; exact here
  by_cases h2 : pc = .ofNat 18446744071579844775
  · subst h2; exact here
  by_cases h3 : pc = .ofNat 18446744071579844778
  · subst h3; exact here
  by_cases h4 : pc = .ofNat 18446744071579844783
  · subst h4; exact here
  exfalso
  have h0' : ¬pc = cmp8Entry := h0
  have h1' : ¬pc = cmp8Entry + 4 := h1
  have h2' : ¬pc = cmp8Entry + 4 + 3 := h2
  have h3' : ¬pc = cmp8Entry + 4 + 3 + 3 := h3
  have h4' : ¬pc = cmp8Entry + 4 + 3 + 3 + 5 := h4
  simp [cmp8Fetch, cmp8Stub, Image.fetchIn, h0', h1', h2', h3', h4'] at here

/-- The callbacks' text is apart from the allowed-IPs image. -/
theorem text_apart {pc : Int64} (inside : Text pc) : AllowedipsImage.fetch pc = none := by
  rcases inside with service | entry
  · exact Text.service_apart service
  · cases other : AllowedipsImage.fetch pc with
    | none => rfl
    | some decoded =>
      have low := Text.allowedips_low other
      simp only [Text.allowedipsLow] at low
      unfold Cmp8.fetch at entry
      cases first : cmp8Fetch pc with
      | some found =>
        have range := (Text.fetchIn_address first (by decide +kernel)).2
        have base : cmp8Entry.toBitVec.toNat + Text.extent cmp8Stub < 18446744071582648656 := by
          decide +kernel
        omega
      | none =>
        rw [first] at entry
        cases second : constCmp8Fetch pc with
        | some found =>
          have range := (Text.fetchIn_address second (by decide +kernel)).2
          have base : constCmp8Entry.toBitVec.toNat + Text.extent constCmp8Stub < 18446744071582648656 := by
            decide +kernel
          omega
        | none => simp [second] at entry

/-- The contract of the allowed-IPs results for `__sanitizer_cov_trace_cmp8`,
from the shared rule. -/
theorem cmp8_contract (rule : Cmp8Rule) (fetch : Int64 → Option Decoded)
    (services : ServiceDecoderAgreement fetch)
    (reading : ∀ pc i, StatementC1CallbackImage.fetch pc = some i → fetch pc = some i) :
    AllowedipsTraceCmp8Contract fetch := by
  intro s ra pc ready frame
  have leaf := cmp8_kcov rule fetch services (c1_agreement fetch reading) s ra pc ready frame
  apply eventually_weaken (historyStep fetch) _ _ _ _ leaf
  rintro t ⟨returned,framed,effect,interior⟩
  exact ⟨returned,framed,effect,fun q member => (interior q member).1.2,
    fun q member => text_apart (interior q member).2⟩

#print axioms cmp8_contract
end Binary.Callback.Cmp8
