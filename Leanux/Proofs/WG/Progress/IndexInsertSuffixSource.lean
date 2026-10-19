import Leanux.Proofs.WG.Progress.IndexProgressSource
import Leanux.Proofs.WG.Progress.NativeSuffixSource

/-! The existing finite original-index evaluation supplies a concrete record
suffix contract. Collision attempts retain their actual consuming search. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Noise

theorem indexInsert_retains (records : List HiddenRecord) (owner : IndexOwner) :
    NativeKeeps records (liftIndex (indexInsert owner)) := by
  intro g
  apply (hoare_iff_run _ _ _).mpr
  intro a out b pre run
  obtain ⟨middle, present, prior⟩ := pre
  cases device : g.dev with
  | none =>
    rw [liftIndex_run_variant, device] at run
    cases run
  | some d =>
    have source := indexInsert_input owner d middle g a device present
    have effect := resolveIndexSearch_outcome (Index.removeOwner owner d.indexTable) middle
    cases resolved : resolveIndexSearch (Index.removeOwner owner d.indexTable) middle with
    | error error =>
      simp only [resolved] at source
      rw [source] at run
      cases run
    | ok pair =>
      rcases pair with ⟨index, rest⟩
      simp only [resolved] at source effect
      obtain ⟨final, after, result, _, remaining⟩ := source
      rw [result] at run
      cases run
      exact ⟨rest, remaining, effect.2.1.trans prior⟩

end Leanux.Proofs.WG.Progress.RecordSuffix
