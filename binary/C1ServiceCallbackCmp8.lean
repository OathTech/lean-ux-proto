import C1ServiceCallbackText
import CallbackCmp8
import StatementC1CallbackImage

/-! `__sanitizer_cov_trace_cmp8` for the allowed-IPs results, from the shared
rule `Binary.Callback.Cmp8.Cmp8Rule`, stated once for results C1 and C2 and
proved in `CallbackCmp8` (`cmp8_rule`; the three `CallbackCmp8*` modules are
taken unchanged from branch `task/binary-c2-wp1` at 414969d4). Nothing is
executed here: this module supplies the rule's agreement premise from C1's
image terms and shows that the callbacks' text is apart from the allowed-IPs
image, which the rule leaves to its user. -/
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

/-- The contract of the allowed-IPs results for `__sanitizer_cov_trace_cmp8`. -/
theorem cmp8_contract (fetch : Int64 → Option Decoded)
    (services : ServiceDecoderAgreement fetch)
    (reading : ∀ pc i, StatementC1CallbackImage.fetch pc = some i → fetch pc = some i) :
    AllowedipsTraceCmp8Contract fetch := by
  intro s ra pc ready frame
  have leaf := cmp8_kcov cmp8_rule fetch services (c1_agreement fetch reading) s ra pc ready frame
  apply eventually_weaken (historyStep fetch) _ _ _ _ leaf
  rintro t ⟨returned,framed,effect,interior⟩
  exact ⟨returned,framed,effect,fun q member => (interior q member).1.2,
    fun q member => text_apart (interior q member).2⟩

#print axioms cmp8_contract
end Binary.Callback.Cmp8
