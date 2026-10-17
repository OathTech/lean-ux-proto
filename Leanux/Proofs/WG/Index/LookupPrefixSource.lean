import Leanux.Proofs.WG.Index.LookupSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

def lookupPrefix (kinds : List IndexKind) (index : Nat) : WG.M LookupState := do
  let entries ← liftIndex (indexBucket index)
  forIn entries (none, false) (lookupStep kinds index)

theorem indexLookup_factor (kinds : List IndexKind) (index : Nat) :
    indexLookup kinds index = (do
      let state ← lookupPrefix kinds index
      lookupFinish state) := by
  rw [indexLookup_source]
  simp [lookupPrefix, bind_assoc]
  rfl

theorem lookupPrefix_returns (kinds : List IndexKind) (index : Nat) (d : Device) :
    Returns (lookupPrefix kinds index) (fun g => g.dev = some d)
      (fun result g => result = selectedState kinds index (bucket index d.indexTable) (none, false) ∧
        g.dev = some d) := by
  intro g ambient device
  let middle := {g with dev := some d}
  obtain ⟨result, final, after, run, selected, state⟩ :=
    lookupScan_returns kinds index (bucket index d.indexTable) (none, false)
      middle middle ambient rfl
  subst final
  refine ⟨result, middle, after, ?_, selected, rfl⟩
  simp [lookupPrefix, liftIndex, indexBucket, getDev, device, modifyDev,
    StateT.run_bind, middle, bucket] at *
  exact run

theorem selectedState_origin (kinds : List IndexKind) (index : Nat)
    (entries : List IndexEntry) (e : IndexEntry)
    (selected : (selectedState kinds index entries (none, false)).1 = some e) :
    e ∈ entries ∧ e.index = index ∧ kinds.contains e.kind = true := by
  unfold selectedState at selected
  cases found : entries.find? (·.index == index) with
  | none => simp [found] at selected
  | some entry =>
    simp only [found] at selected
    split at selected
    · simp only [Option.some.injEq] at selected
      subst e
      exact ⟨List.mem_of_find?_eq_some found, by simpa using List.find?_some found, by assumption⟩
    · simp at selected

end Leanux.Proofs.WG.Index
