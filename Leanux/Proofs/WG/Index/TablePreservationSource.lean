import Leanux.Proofs.WG.Index.NewlinkFrames
import Leanux.Proofs.WG.Index.OwnerCreation
import Leanux.Proofs.WG.Index.HandshakeClaims
import Leanux.Proofs.WG.Index.SessionOwners

/-! Existing table-invariant contracts over the original native operations.
The numeric and owner/bound facts are combined on the same run. -/
set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

/-- Combine numeric uniqueness and owner/allocation bounds on the same original run. -/
theorem createInitiation_tables (pid : PeerId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ createInitiation pid
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  cases device : g.dev with
  | none =>
    simp [createInitiation, getPeer, getDev, device, invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    have safe := pre d device
    obtain ⟨di, hi, indices⟩ := (ensures_iff _ _ _).mpr (createInitiation_indices_spec pid)
      g ambient result final after ⟨d, device, safe.1⟩ run
    obtain ⟨doo, ho, owners, bounded⟩ := (ensures_iff _ _ _).mpr (createInitiation_owners_spec pid)
      g ambient result final after ⟨d, device, safe.2.1, safe.2.2⟩ run
    intro df present
    rw [present] at hi ho
    cases hi
    cases ho
    exact ⟨indices, owners, bounded⟩

theorem indexRemove_tables (owner : IndexOwner) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ liftIndex (indexRemove owner)
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  cases device : g.dev with
  | none =>
    rw [liftIndex_run_variant, device] at run
    cases run
  | some d =>
    obtain ⟨r, out, tail, execution, changed⟩ := indexRemove_exact owner d g ambient device
    rw [run] at execution
    cases execution
    intro df present
    rw [changed] at present
    cases present
    have safe := pre d device
    refine ⟨remove_indices owner _ safe.1, remove_owners owner _ safe.2.1, ?_⟩
    intro e member id own
    exact safe.2.2 e (List.mem_filter.mp member).1 id own

/-- Combine numeric uniqueness and owner/allocation bounds on the same original run. -/
theorem createResponse_tables (pid : PeerId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ createResponse pid
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  cases device : g.dev with
  | none =>
    simp [createResponse, getPeer, getDev, device, invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    have safe := pre d device
    obtain ⟨di, hi, indices⟩ := (ensures_iff _ _ _).mpr (createResponse_indices_spec pid)
      g ambient result final after ⟨d, device, safe.1⟩ run
    obtain ⟨doo, ho, owners, bounded⟩ := (ensures_iff _ _ _).mpr (createResponse_owners_spec pid)
      g ambient result final after ⟨d, device, safe.2.1, safe.2.2⟩ run
    intro df present
    rw [present] at hi ho
    cases hi
    cases ho
    exact ⟨indices, owners, bounded⟩

/-- Combine numeric uniqueness and owner/allocation bounds on the same original run. -/
theorem beginSession_tables (pid : PeerId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ beginSession pid
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  cases device : g.dev with
  | none =>
    simp [beginSession, getPeer, getDev, device, invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    have safe := pre d device
    obtain ⟨di, hi, indices⟩ := (ensures_iff _ _ _).mpr (beginSession_indices_spec pid)
      g ambient result final after ⟨d, device, safe.1⟩ run
    obtain ⟨doo, ho, owners, bounded⟩ := (ensures_iff _ _ _).mpr (beginSession_owners_spec pid)
      g ambient result final after ⟨d, device, safe.2.1, safe.2.2⟩ run
    intro df present
    rw [present] at hi ho
    cases hi
    cases ho
    exact ⟨indices, owners, bounded⟩

end Leanux.Proofs.WG.Index
