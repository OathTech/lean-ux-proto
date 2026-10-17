import Leanux.Proofs.WG.Index.OwnerCoherenceClearFrames
import Leanux.Proofs.WG.Noise.RotationSource
import Leanux.Proofs.WG.Noise.ClearSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

/-- Responder confirmation preserves all hashed-owner coherence on normal
return. Neither successful confirmation nor resident or distinct slot keys are
assumed; the actual first peer read supplies the effect model's residency. -/
theorem receivedWithKeypair_owner_coherent (pid : PeerId) (received : KeypairId) :
    Campaign2.Ensures (receivedWithKeypair pid received) View.OwnerCoherentSafe
      (fun _ s => View.OwnerCoherentSafe s) := by
  intro g ambient ok out after pre run
  cases device : g.dev with
  | none =>
    simp [receivedWithKeypair, getPeer, getDev, device, invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [receivedWithKeypair, getPeer, getDev, device, resident,
        invariant, AmbientM.invariant] at run
      cases run
    | some p =>
      obtain ⟨final, present, effect⟩ := receivedWithKeypair_effect pid received d p resident
        g ambient ok out after device run
      have coherent : HashedOwnersCoherent final := by
        by_cases matched : p.keypairNext = some received
        · obtain ⟨_, steps⟩ := (by simpa [ConfirmationEffect, matched] using effect :
            ok = true ∧ RotationRun pid d (confirmationPlan p received) final)
          exact rotationRun_owner_coherent steps (pre d device)
        · have same : final = d := (by simpa [ConfirmationEffect, matched] using effect :
            ok = false ∧ final = d).2
          rw [same]
          exact pre d device
      intro observed observedDevice
      change out.dev = some observed at observedDevice
      rw [present] at observedDevice
      cases observedDevice
      exact coherent

/-- Original key clearing preserves coherence for every normal return, without
reference budgets, slot distinctness, residency or readiness premises. Refused
puts remain Stops; this does not assert that all three puts complete. -/
theorem keypairsClear_owner_coherent (pid : PeerId) :
    Campaign2.Ensures (keypairsClear pid) View.OwnerCoherentSafe
      (fun _ s => View.OwnerCoherentSafe s) := by
  intro g ambient result out after pre run
  cases device : g.dev with
  | none =>
    simp [keypairsClear, getPeer, getDev, device, invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [keypairsClear, getPeer, getDev, device, resident,
        invariant, AmbientM.invariant] at run
      cases run
    | some p =>
      obtain ⟨final, present, steps⟩ := keypairsClear_effect pid d p resident
        g ambient result out after device run
      have coherent := clearRun_owner_coherent steps (pre d device)
      intro observed observedDevice
      change out.dev = some observed at observedDevice
      rw [present] at observedDevice
      cases observedDevice
      exact coherent

end Leanux.Proofs.WG.Index
