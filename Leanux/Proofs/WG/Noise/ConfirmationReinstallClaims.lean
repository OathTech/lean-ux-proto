import Leanux.Proofs.WG.Noise.ConfirmationReinstallSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

open ConfirmationReinstallWitness

/-- Two normal confirmations can concern the same resident key when a
caller directly reinstalls it. This is an arbitrary helper-call-domain witness;
it does not refute uniqueness for fresh beginSession installations. -/
theorem confirmation_same_allocation_reinstallation :
    ∃ d : Device, ∃ k : Keypair,
      d.keypairs[0]? = some k ∧ k.internalId = 17 ∧
      Campaign2.Observes calls (fun entry => entry.wg.device = some d)
        (fun entry out => ∃ after final,
          out = .ok ((true, true), after) ∧ after.wg.device = some final ∧
          final.keypairs[0]? = some k ∧
          after.wg.keypairCounter = entry.wg.keypairCounter ∧
          final.nextKeypairId = d.nextKeypairId) := by
  refine ⟨device, key, confirmationReinstallWitness_shape.2.1, rfl, ?_⟩
  intro g ambient pre
  obtain ⟨result, final, inputs, run, answer, counter, d, hd, hk, cursor, rest⟩ :=
    confirmationReinstallWitness_returns g.keypairCounter g ambient ⟨pre, rfl⟩
  subst result
  refine ⟨Campaign2.snapshot final inputs, d, ?_, hd, hk, counter, cursor⟩
  simp [Campaign2.observeResult, run, Except.map]


end Leanux.Proofs.WG.Noise
