import Leanux.Proofs.WG.Progress.JitterProgressSource
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Projected total outcomes of recorded jitter. The actual product lift retains
the original fixture observations as well as WG and Ambient state. Recordless
execution and scheduler progress are outside these contracts. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Proofs.WG.TimerDiscipline

theorem jitter_record_outcome (site : JitterSite) (records : List HiddenRecord) :
    Campaign2.Product.Observes (liftWG (jitterBelowRekeyTimeout site.hiddenSite))
      (fun s => s.ambient.hidden = some records)
      (fun entry outcome => outcome =
        match resolveJitterSearch site records with
        | .error error => .error error
        | .ok (jitter, rest) => .ok (jitter,
            {entry with ambient := {entry.ambient with hidden := some rest}})) := by
  intro w present
  change Campaign2.Product.observeResult
    (((jitterBelowRekeyTimeout site.hiddenSite).run w.wg).run w.ambient >>= fun ((value, g), ambient) =>
      Except.ok (value, {w with wg := g, ambient})) = _
  rw [jitter_input site records w.wg w.ambient present]
  cases resolution : resolveJitterSearch site records with
  | error error => rfl
  | ok pair => rcases pair with ⟨jitter, rest⟩; rfl

theorem jitter_record_progress (site : JitterSite) (records : List HiddenRecord) :
    Campaign2.Product.Observes (liftWG (jitterBelowRekeyTimeout site.hiddenSite))
      (fun s => s.ambient.hidden = some records)
      (fun entry outcome =>
        (∃ message, outcome = .error (.hidden message)) ∨
        ∃ jitter rest, outcome = .ok (jitter,
            {entry with ambient := {entry.ambient with hidden := some rest}}) ∧
          jitter < HZ / 3 ∧ rest.IsSuffix records ∧ rest.length < records.length) := by
  intro w present
  have source := jitter_record_outcome site records w present
  have shape := resolveJitterSearch_outcome site records
  cases resolution : resolveJitterSearch site records with
  | error error =>
    simp only [resolution] at source shape
    obtain ⟨message, rfl⟩ := shape
    exact Or.inl ⟨message, source⟩
  | ok pair =>
    rcases pair with ⟨jitter, rest⟩
    simp only [resolution] at source shape
    exact Or.inr ⟨jitter, rest, source, shape⟩
end Leanux.Proofs.WG.Progress
