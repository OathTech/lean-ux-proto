import Leanux.Proofs.WG.Index.IndexFieldFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

/-! Numeric index uniqueness is preserved by the native table operations through
their guarded device adapter. Device residency remains an explicit premise. -/
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Config Std.Do

theorem indexRemove_indices_spec (owner : IndexOwner) :
    ⦃fun w => ⌜IndicesSafe w⌝⦄ liftIndex (indexRemove owner) ⦃⇓? _ w => ⌜IndicesSafe w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w ambient result final after pre run
  obtain ⟨d, device, unique⟩ := pre
  obtain ⟨r, v, next, hr, hd⟩ := indexRemove_exact owner d w ambient device
  rw [run] at hr
  cases hr
  exact ⟨_, hd, remove_indices owner _ unique⟩

theorem indexInsert_indices_spec (owner : IndexOwner) :
    ⦃fun w => ⌜IndicesSafe w⌝⦄ liftIndex (indexInsert owner) ⦃⇓? _ w => ⌜IndicesSafe w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w ambient result final after pre run
  obtain ⟨d, device, unique⟩ := pre
  obtain ⟨hd, fresh⟩ := indexInsert_exact owner d w ambient result final after device run
  refine ⟨_, hd, insert_indices owner result _ unique ?_⟩
  intro e member
  have absent := List.any_eq_false.mp fresh e member
  have different : e.index ≠ result := by simpa using absent
  exact Ne.symm different

theorem indexReplace_indices_spec (pid : PeerId) (kp : KeypairId) :
    ⦃fun w => ⌜IndicesSafe w⌝⦄ liftIndex (indexReplaceHandshake pid kp) ⦃⇓? _ w => ⌜IndicesSafe w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w ambient result final after pre run
  obtain ⟨d, device, unique⟩ := pre
  obtain ⟨r, v, next, hr, value, hd⟩ := indexReplace_exact pid kp d w ambient device
  rw [run] at hr
  cases hr
  refine ⟨_, hd, ?_⟩
  cases result
  · exact unique
  · exact replace_indices pid kp _ unique

end Leanux.Proofs.WG.Index
