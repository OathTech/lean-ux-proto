import Leanux.Proofs.WG.Index.PeerWords

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

theorem lookupFinish_miss (stopped : Bool) (d : Device) :
    Returns (lookupFinish (none, stopped)) (fun g => g.dev = some d)
      (fun result g => result = none ∧ g.dev = some d) := by
  intro g ambient device
  let after := recordStep (if stopped then ambient else recordStep ambient .idxWalk false)
    .idxFound false
  refine ⟨none, g, after, ?_, rfl, device⟩
  cases stopped <;> simp [lookupFinish, branch, AmbientM.branch, after, recordStep] <;> rfl

theorem indexLookup_miss (kinds : List IndexKind) (index : Nat) (d : Device)
    (noMatch : ∀ e, d.indexTable.find? (·.index == index) = some e →
      kinds.contains e.kind = false) :
    Returns (indexLookup kinds index) (fun g => g.dev = some d)
      (fun result g => result = none ∧ g.dev = some d) := by
  rw [indexLookup_factor]
  apply returns_bind _ _ (lookupPrefix_returns kinds index d)
  intro state g ambient pre
  obtain ⟨eq, device⟩ := pre
  have missing : state.1 = none := by
    rw [eq]
    simp only [selectedState, bucket_find]
    cases h : d.indexTable.find? (·.index == index) with
    | none => rfl
    | some e => simp [noMatch e h]
  obtain ⟨entry, stopped⟩ := state
  simp only at missing
  subst entry
  exact lookupFinish_miss stopped d g ambient device

end Leanux.Proofs.WG.Index
