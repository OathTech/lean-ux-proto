import Leanux.Proofs.WG.AuthenticatedEffects.CausalCallbackQuietActors

/-! Append-only quiet callback histories retain any predicate closed under
quiet suffixes. Full history positions are unchanged; no reindexing is used. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.CallbackQuiet
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity
variable {F : Type} {ρ : Event → Option F} {Safe : List Event → Prop}

private theorem suffix_quiet {history suffix : List Event}
    (same : (history ++ suffix).filterMap ρ = history.filterMap ρ) :
    ∀ event ∈ suffix, ρ event = none := by
  apply List.forall_none_of_filterMap_eq_nil
  exact List.append_right_eq_self.mp (by simpa only [List.filterMap_append] using same)

theorem state_safe (quiet : StateQuiet ρ body)
    (extend : ∀ history suffix, Safe history → (∀ event ∈ suffix, ρ event = none) → Safe (history ++ suffix)) :
    Driver.StateHistorySafe Safe body := by
  intro w a history hi
  obtain ⟨suffix,grown⟩ := quiet.1 w a history
  have preserved := quiet.2 w a history
  change (runPrefix (body.run w) a history).2.filterMap ρ = _ at preserved
  rw [grown] at preserved
  have good := extend history suffix hi (suffix_quiet preserved)
  refine ⟨suffix,grown,?_,?_⟩
  · simpa only [grown] using good
  · cases (runPrefix (body.run w) a history).1 <;> first | trivial | simpa only [grown] using good

theorem product_safe (quiet : ProductQuiet ρ body)
    (extend : ∀ history suffix, Safe history → (∀ event ∈ suffix, ρ event = none) → Safe (history ++ suffix)) :
    Driver.ProductHistorySafe Safe body := by
  intro w history hi
  obtain ⟨suffix,grown⟩ := quiet.1 w history
  have preserved := quiet.2 w history
  rw [grown] at preserved
  have good := extend history suffix hi (suffix_quiet preserved)
  refine ⟨suffix,grown,?_,?_⟩
  · simpa only [grown] using good
  · cases (runPrefix body w history).1 <;> first | trivial | simpa only [grown] using good

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.CallbackQuiet
