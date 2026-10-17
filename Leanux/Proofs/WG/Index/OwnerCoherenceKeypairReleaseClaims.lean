import Leanux.Proofs.WG.Index.OwnerCoherenceKeypairReleaseFrames
import Leanux.Proofs.WG.Noise.ClearSource
import Leanux.Proofs.WG.Config.KeyReferences
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

/-- Every normally returning keypair put preserves local hashed-owner
coherence, including retained NULL-word keys. No readiness, residency,
reference bound or detachment assumption is added to the entry invariant. -/
theorem keypairPut_owner_coherent (key : Option KeypairId) (now : Bool) :
    Campaign2.Ensures (keypairPut key now) View.OwnerCoherentSafe
      (fun _ s => View.OwnerCoherentSafe s) := by
  intro g ambient result final after pre run
  cases device : g.dev with
  | none =>
    cases key with
    | none =>
      simp [keypairPut, branch, AmbientM.branch] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
    | some id =>
      simp [keypairPut, branch, AmbientM.branch, getKeypair, getDev, device,
        invariant, AmbientM.invariant] at run
      cases run
  | some d =>
    have entry : HashedOwnersCoherent d := pre d device
    have finish (out : Device) (present : final.dev = some out)
        (safe : HashedOwnersCoherent out) : View.OwnerCoherentSafe (Campaign2.snapshot final after) := by
      intro actual actualDevice
      change final.dev = some actual at actualDevice
      rw [present] at actualDevice
      cases actualDevice
      exact safe
    cases now with
    | true =>
      obtain ⟨out, present, effect⟩ :=
        Noise.clearPut_effect key d g ambient result final after device run
      apply finish out present
      cases effect with
      | null => exact entry
      | present d id k resident live word =>
        exact releasedDevice_owner_coherent d id k true resident live entry
    | false =>
      cases key with
      | none =>
        obtain ⟨u, out, next, actual, present⟩ := Config.keypairPut_none d g ambient device
        rw [run] at actual
        cases actual
        exact finish d present entry
      | some id =>
        cases resident : d.keypairs[id]? with
        | none =>
          simp [keypairPut, branch, AmbientM.branch, getKeypair, getDev, device,
            resident, invariant, AmbientM.invariant] at run
          cases run
        | some k =>
          by_cases zero : k.refcount = 0
          · simp [keypairPut, branch, AmbientM.branch, getKeypair, getDev, device,
              resident, setKeypair, modifyDev, refcountDecAndTest, zero,
              branchCmp, AmbientM.branchCmp, unsupported, AmbientM.unsupported] at run
            cases run
          · have live : 0 < k.refcount := by omega
            by_cases last : k.refcount = 1
            · cases word : k.peer with
              | none =>
                simp [keypairPut, branch, AmbientM.branch, getKeypair, getDev, device,
                  resident, setKeypair, modifyDev, refcountDecAndTest, last,
                  branchCmp, AmbientM.branchCmp, IndexOwner.peerDeref, IndexOwner.peerWord,
                  word, unsupported, AmbientM.unsupported] at run
                cases run
              | some pid =>
                obtain ⟨u, out, next, actual, present⟩ :=
                  keypairPut_exact id false d k resident live (by simp [word]) g ambient device
                rw [run] at actual
                cases actual
                exact finish _ present (releasedDevice_owner_coherent d id k false resident live entry)
            · obtain ⟨u, out, next, actual, present⟩ :=
                Config.keypairPut_retained id d k resident (by omega) g ambient device
              rw [run] at actual
              cases actual
              apply finish _ present
              simpa [releasedDevice, unhashKeypair, last, Config.withKeypair] using
                releasedDevice_owner_coherent d id k false resident live entry

end Leanux.Proofs.WG.Index
