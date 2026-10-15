import Leanux.Proofs.WG.Progress.CutSource

set_option autoImplicit false

namespace Leanux.Proofs.WG.Progress
open Leanux Campaign2

theorem source_cut_outcome (sites : List HiddenSite) (records : List HiddenRecord) :
    Campaign2.Observes (skipCutSites sites) (fun entry => entry.ambient.hidden = some records)
      (CutOutcome sites records) := by
  intro w present
  rcases skipCutSites_outcome sites w records present with
    ⟨taken, rest, final, execution, hidden, progress⟩ |
    ⟨message, execution, bad, _⟩
  · simp only [observeResult, execution, Except.map]
    exact ⟨rest, hidden, progress⟩
  · simp only [observeResult, execution, Except.map]
    exact ⟨message, rfl, bad⟩

theorem source_cut_returns (sites : List HiddenSite) (records : List HiddenRecord)
    (accepted : CutAccepted sites records) :
    Campaign2.Returns (skipCutSites sites) (fun entry => entry.ambient.hidden = some records)
      (fun taken final => ∃ rest, final.ambient.hidden = some rest ∧ CutProgress sites records taken rest) := by
  intro w present
  rcases skipCutSites_outcome sites w records present with
    ⟨taken, rest, final, execution, hidden, progress⟩ |
    ⟨_, _, _, rejected⟩
  · exact ⟨taken, final, execution, rest, hidden, progress⟩
  · exact False.elim (rejected accepted)

end Leanux.Proofs.WG.Progress
