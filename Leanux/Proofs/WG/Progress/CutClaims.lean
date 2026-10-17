import Leanux.Proofs.WG.Progress.CutSource

set_option autoImplicit false

namespace Leanux.Proofs.WG.Progress
open Leanux Campaign2

theorem source_cut_outcome (sites : List HiddenSite) (records : List HiddenRecord) :
    Campaign2.Observes (skipCutSites sites) (fun entry => entry.ambient.hidden = some records)
      (CutOutcome sites records) := by
  intro g ambient present
  rcases skipCutSites_outcome sites ambient records present with
    ⟨taken, rest, final, execution, hidden, progress⟩ |
    ⟨message, execution, bad, _⟩
  · change CutOutcome sites records (snapshot g ambient)
      (observeResult ((AmbientM.skipCutSites sites).run ambient >>=
        fun (taken, final) => Except.ok ((taken, g), final)))
    rw [execution]
    dsimp only [Except.bind, observeResult, Except.map, CutOutcome, snapshot]
    exact ⟨rest, hidden, progress⟩
  · change CutOutcome sites records (snapshot g ambient)
      (observeResult ((AmbientM.skipCutSites sites).run ambient >>=
        fun (taken, final) => Except.ok ((taken, g), final)))
    rw [execution]
    dsimp only [Except.bind, observeResult, Except.map, CutOutcome, snapshot]
    exact ⟨message, rfl, bad⟩

theorem source_cut_returns (sites : List HiddenSite) (records : List HiddenRecord)
    (accepted : CutAccepted sites records) :
    Campaign2.Returns (skipCutSites sites) (fun entry => entry.ambient.hidden = some records)
      (fun taken final => ∃ rest, final.ambient.hidden = some rest ∧ CutProgress sites records taken rest) := by
  intro g ambient present
  rcases skipCutSites_outcome sites ambient records present with
    ⟨taken, rest, final, execution, hidden, progress⟩ |
    ⟨_, _, _, rejected⟩
  · refine ⟨taken, g, final, ?_, rest, hidden, progress⟩
    change ((AmbientM.skipCutSites sites).run ambient >>=
      fun (taken, final) => Except.ok ((taken, g), final)) = _
    rw [execution]
    rfl
  · exact False.elim (rejected accepted)

end Leanux.Proofs.WG.Progress
