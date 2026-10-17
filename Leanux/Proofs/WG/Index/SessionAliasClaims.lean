import Leanux.Proofs.WG.Index.SessionAliasSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

open SessionAliasWitness

/-- Local table/owner/store invariants do not rule out allocating an identity
already named by an old slot. The actual successful session then loses owner
coherence, and its immediate actual lookup stops. This is not initialized
reachability or a mirror/kernel defect claim. -/
theorem session_alias_owner_coherence_counterexample (counter : Nat) :
    DeviceTablesSafe device ∧ HashedOwnersCoherent device ∧ KeypairStoreBounded device ∧
    Campaign2.Observes (beginSession 0) (input counter)
      (fun _ out => ∃ s final, out = .ok (true,s) ∧ s.wg.device = some final ∧
        final.keypairs[1]? = none ∧ final.indexTable = [published] ∧
        DeviceTablesSafe final ∧ ¬ HashedOwnersCoherent final ∧
        s.wg.keypairCounter = counter + 1) ∧
    Campaign2.Observes (do let _ ← beginSession 0; indexLookup [.keypair] 7) (input counter)
      (fun _ out => out = .error (.invariant "dangling keypair 1")) := by
  refine ⟨sessionAlias_entry.1,sessionAlias_entry.2.1,sessionAlias_entry.2.2,?_,?_⟩
  · intro g ambient pre
    obtain ⟨ok,final,after,run,success,d,device,absent,table,cursor,count⟩ :=
      sessionAlias_returns counter g ambient pre
    subst ok
    refine ⟨Campaign2.snapshot final after,d,?_,device,absent,table,?_,?_,count⟩
    · simp [Campaign2.observeResult,run,Except.map]
    · simp [DeviceTablesSafe,UniqueIndices,UniqueOwners,KeypairOwnersBounded,table,cursor,published]
    · intro coherent
      obtain ⟨pid,p,word,_⟩ := coherent published (by simp [table])
      simp [ownerWord,published,absent] at word
  · intro g ambient pre
    obtain ⟨ok,final,after,run,success,d,device,absent,table,_,_⟩ :=
      sessionAlias_returns counter g ambient pre
    have stopped := sessionAlias_lookup_stops final after d device table absent
    change Campaign2.observeResult
      ((((beginSession 0).run g).run ambient >>= fun ((_,middle),inputs) =>
        ((indexLookup [.keypair] 7).run middle).run inputs)) = _
    rw [run]
    change Campaign2.observeResult (((indexLookup [.keypair] 7).run final).run after) = _
    rw [stopped]
    rfl


end Leanux.Proofs.WG.Index
