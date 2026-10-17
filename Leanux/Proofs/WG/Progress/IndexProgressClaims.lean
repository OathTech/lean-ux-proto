import Leanux.Proofs.WG.Progress.IndexProgressSource
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Projected whole-call contracts for recorded index insertion. The recordless
domain filter, table-wide uniqueness and owner residency are separate claims. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Proofs.WG.Index

theorem index_record_outcome (owner : IndexOwner) (d : Device) (records : List HiddenRecord) :
    Campaign2.Observes (liftIndex (indexInsert owner))
      (fun s => s.wg.device = some d ∧ s.ambient.hidden = some records)
      (fun _ outcome =>
        match resolveIndexSearch (removeOwner owner d.indexTable) records with
        | .error error => outcome = .error error
        | .ok (index, rest) => ∃ final,
          outcome = .ok (index, final) ∧
          final.wg.device = some {d with indexTable :=
            {index, owner} :: removeOwner owner d.indexTable} ∧
          final.ambient.hidden = some rest) := by
  intro g ambient pre
  have source := indexInsert_input owner d records g ambient pre.1 pre.2
  cases resolution : resolveIndexSearch (removeOwner owner d.indexTable) records with
  | error error =>
    simp only [resolution] at source ⊢
    rw [source]
    rfl
  | ok pair =>
    rcases pair with ⟨index, rest⟩
    simp only [resolution] at source ⊢
    obtain ⟨final, after, run, device, hidden⟩ := source
    exact ⟨Campaign2.snapshot final after, by rw [run]; rfl, device, hidden⟩

theorem index_record_progress (owner : IndexOwner) (d : Device) (records : List HiddenRecord) :
    Campaign2.Observes (liftIndex (indexInsert owner))
      (fun s => s.wg.device = some d ∧ s.ambient.hidden = some records)
      (fun _ outcome =>
        (∃ message, outcome = .error (.hidden message)) ∨
        ∃ index rest final, outcome = .ok (index, final) ∧
          (removeOwner owner d.indexTable).any (·.index == index) = false ∧
          rest.IsSuffix records ∧ rest.length < records.length ∧
          final.wg.device = some {d with indexTable :=
            {index, owner} :: removeOwner owner d.indexTable} ∧
          final.ambient.hidden = some rest) := by
  intro g ambient pre
  have source := index_record_outcome owner d records g ambient pre
  have shape := resolveIndexSearch_outcome (removeOwner owner d.indexTable) records
  cases resolution : resolveIndexSearch (removeOwner owner d.indexTable) records with
  | error error =>
    simp only [resolution] at source shape
    obtain ⟨message, rfl⟩ := shape
    exact Or.inl ⟨message, source⟩
  | ok pair =>
    rcases pair with ⟨index, rest⟩
    simp only [resolution] at source shape
    obtain ⟨final, run, device, hidden⟩ := source
    exact Or.inr ⟨index, rest, final, run, shape.1, shape.2.1, shape.2.2, device, hidden⟩


end Leanux.Proofs.WG.Progress
