import Leanux.Proofs.WG.RetirementSecurity.Credits

/-! Actual successful key-reference acquisition adds one occurrence to the
same allocation. Count-zero and saturation arms remain original failures or
refusals; the ledger never manufactures a reference from available slack. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing

structure GetEffect (id : KeypairId) (k : Keypair) (before after : WGWorld) : Prop where
  positive : 0 < k.refcount
  bounded : k.refcount + 1 < 2 ^ 31
  frontier : after.keypairCounter = before.keypairCounter
  selected : keyAt after id = some {k with refcount := k.refcount + 1}
  others : ∀ other, other ≠ id → keyAt after other = keyAt before other

theorem get_effect (id : KeypairId) (w v : WGWorld) (a b : Ambient)
    (d : Device) (k : Keypair)
    (device : w.dev = some d) (resident : d.keypairs[id]? = some k)
    (run : ((keypairGet (some id)).run w).run a = .ok ((some id,v),b)) :
    GetEffect id k w v := by
  by_cases zero : k.refcount = 0 <;> by_cases overflow : k.refcount + 1 ≥ 2 ^ 31
  all_goals have wrap : (2147483647 ≤ k.refcount) ↔ (k.refcount + 1 ≥ 2 ^ 31) := by omega
  all_goals simp [keypairGet,refcountIncNotZero,branch,branchCmp,getKeypair,getDev,
    device,resident,zero,overflow,wrap,setKeypair,modifyDev,unsupported,
    AmbientM.branch,AmbientM.branchCmp,AmbientM.unsupported,
    StateT.run_bind,StateT.run_get,StateT.run_pure] at run
  all_goals obtain ⟨rfl,rfl⟩ := run
  all_goals constructor
  all_goals first
    | omega
    | rfl
    | (intro other different
       simp [keyAt,device,Std.TreeMap.getElem?_insert,Ne.symm different])
    | (simp [keyAt])

theorem get_retains (kp : Option KeypairId) (w v : WGWorld) (a b : Ambient)
    (result : Option KeypairId)
    (run : ((keypairGet kp).run w).run a = .ok ((result,v),b)) : Retains w v := by
  cases kp with
  | none =>
    simp [keypairGet,branch,AmbientM.branch] at run
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
    exact Retains.refl w
  | some id =>
    cases device : w.dev with
    | none =>
      simp [keypairGet,branch,AmbientM.branch,getKeypair,getDev,device,
        invariant,AmbientM.invariant] at run
      cases run
    | some d =>
      cases resident : d.keypairs[id]? with
      | none =>
        simp [keypairGet,branch,AmbientM.branch,getKeypair,getDev,device,resident,
          invariant,AmbientM.invariant] at run
        cases run
      | some k =>
        by_cases zero : k.refcount = 0 <;> by_cases overflow : k.refcount + 1 ≥ 2 ^ 31
        all_goals try omega
        all_goals have wrap : (2147483647 ≤ k.refcount) ↔ (k.refcount + 1 ≥ 2 ^ 31) := by omega
        all_goals simp [keypairGet,refcountIncNotZero,branch,branchCmp,getKeypair,getDev,
          device,resident,zero,overflow,wrap,setKeypair,modifyDev,unsupported,
          AmbientM.branch,AmbientM.branchCmp,AmbientM.unsupported,
          StateT.run_bind,StateT.run_get,StateT.run_pure] at run
        all_goals obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
        · exact Retains.refl w
        · refine ⟨rfl,?_⟩
          intro other current found
          by_cases same : id = other
          · subst other
            simp [keyAt] at found
            cases found
            exact ⟨k,by simp [keyAt,device,resident],rfl⟩
          · have old : keyAt w other = some current := by
              simpa [keyAt,device,Std.TreeMap.getElem?_insert,same] using found
            exact ⟨current,old,rfl⟩

theorem get_nonce_projection (kp : Option KeypairId) (w v : WGWorld) (a b : Ambient)
    (result : Option KeypairId)
    (run : ((keypairGet kp).run w).run a = .ok ((result,v),b)) :
    v.keypairCounter = w.keypairCounter ∧
      ∀ id k, keyAt v id = some k → ∃ old, keyAt w id = some old ∧
        k.internalId = old.internalId ∧ k.sendingCounter = old.sendingCounter := by
  have kept := get_retains kp w v a b result run
  refine ⟨kept.counter,?_⟩
  intro id k found
  obtain ⟨old,ho,eq⟩ := kept.keys id k found
  exact ⟨old,ho,by simpa only [keyCore] using congrArg Keypair.internalId eq,
    by simpa only [keyCore] using congrArg Keypair.sendingCounter eq⟩

namespace Credits

theorem Exact.get (account : Exact credits w) (id : KeypairId) (k : Keypair)
    (found : keyAt w id = some k) (a b : Ambient)
    (run : ((keypairGet (some id)).run w).run a = .ok ((some id,v),b)) :
    Exact (⟨id,k.internalId⟩ :: credits) v := by
  cases device : w.dev with
  | none => simp [keyAt,device] at found
  | some d =>
    have resident : d.keypairs[id]? = some k := by simpa [keyAt,device] using found
    have effect := get_effect id w v a b d k device resident run
    intro other
    have before := account other
    by_cases same : other = (⟨id,k.internalId⟩ : Allocation)
    · subst other
      simpa only [List.count_cons_self,balance,found,GetEffect.selected effect,
        ↓reduceIte] using congrArg (· + 1) before
    · have count : ((⟨id,k.internalId⟩ : Allocation) :: credits).count other = credits.count other := by
        simp [Ne.symm same]
      rw [count]
      by_cases slot : other.slot = id
      · have different : k.internalId ≠ other.stamp := by
          intro equal
          apply same
          cases other
          simp_all
        simpa [balance,slot,found,effect.selected,different] using before
      · simpa only [balance,effect.others other.slot slot] using before

end Credits
end Leanux.Proofs.WG.RetirementSecurity
