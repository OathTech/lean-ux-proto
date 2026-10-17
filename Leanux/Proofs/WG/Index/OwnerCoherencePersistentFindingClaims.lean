import Leanux.Proofs.WG.Index.OwnerCoherencePersistentFindingSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG
open PersistentOwnerWitness

/-- A whole persistent-keepalive callback can return normally from a locally
coherent arbitrary state and leave a hashed owner without its peer. The selected
keypair names another peer; no initialized reachability is asserted. -/
theorem expiredPersistent_ownerCoherentSafe_counterexample :
    ∃ d : Device, HashedOwnersCoherent d ∧
      Campaign2.Observes (expiredSendPersistentKeepalive 0)
        (fun s => s.wg.device = some d ∧ s.ambient.hidden = some [clock])
        (fun _ out => ∃ final, out = .ok ((), final) ∧ ¬ View.OwnerCoherentSafe final) := by
  refine ⟨device, persistentOwnerWitness_coherent, ?_⟩
  intro g ambient pre
  obtain ⟨value, current, inputs, run, final, hd, absent, key, member⟩ :=
    persistentOwnerWitness_returns g ambient pre
  cases value
  refine ⟨Campaign2.snapshot current inputs, ?_, ?_⟩
  · simp [Campaign2.observeResult, run, Except.map]
  · intro safe
    obtain ⟨pid, p, word, found, _, _⟩ := safe final hd entry member
    have same : pid = 0 := by
      simpa [ownerWord, entry, key, dangling] using word.symm
    subst pid
    rw [absent] at found
    cases found


end Leanux.Proofs.WG.Index
