import Leanux.Proofs.WG.Noise.ClearSource
import Leanux.Proofs.WG.Config.KeyReferences
import Leanux.Proofs.WG.Index.Release
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

/-- Exact normal device outcome for both key-put modes. Retained nullable
owner words are permitted; invalid getters/counts and dereference failures keep
their original Stops rather than supplying a fabricated final device. -/
theorem keypairPut_normal_effect (key : Option KeypairId) (now : Bool)
    (g out : WGWorld) (ambient after : Ambient) (result : Unit)
    (run : ((keypairPut key now).run g).run ambient = .ok ((result,out),after)) :
    (key = none ∧ out.dev = g.dev) ∨
      ∃ id d k, key = some id ∧ g.dev = some d ∧ d.keypairs[id]? = some k ∧
        0 < k.refcount ∧ out.dev = some (releasedDevice d id k now) := by
  cases device : g.dev with
  | none =>
    cases key with
    | none =>
      simp [keypairPut,branch,AmbientM.branch] at run
      rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
      exact Or.inl ⟨rfl,device⟩
    | some id =>
      simp [keypairPut,branch,AmbientM.branch,getKeypair,getDev,device,
        invariant,AmbientM.invariant] at run
      cases run
  | some d =>
    cases now with
    | true =>
      obtain ⟨final,present,effect⟩ := clearPut_effect key d g ambient result out after device run
      cases effect with
      | null => exact Or.inl ⟨rfl,present⟩
      | present d id k resident live word =>
        exact Or.inr ⟨id,d,k,rfl,rfl,resident,live,present⟩
    | false =>
      cases key with
      | none =>
        obtain ⟨u,final,next,actual,present⟩ := Config.keypairPut_none d g ambient device
        rw [run] at actual
        cases actual
        exact Or.inl ⟨rfl,present⟩
      | some id =>
        cases resident : d.keypairs[id]? with
        | none =>
          simp [keypairPut,branch,AmbientM.branch,getKeypair,getDev,device,
            resident,invariant,AmbientM.invariant] at run
          cases run
        | some k =>
          by_cases zero : k.refcount = 0
          · simp [keypairPut,branch,AmbientM.branch,getKeypair,getDev,device,
              resident,setKeypair,modifyDev,refcountDecAndTest,zero,
              branchCmp,AmbientM.branchCmp,unsupported,AmbientM.unsupported] at run
            cases run
          · have live : 0 < k.refcount := by omega
            by_cases last : k.refcount = 1
            · cases word : k.peer with
              | none =>
                simp [keypairPut,branch,AmbientM.branch,getKeypair,getDev,device,
                  resident,setKeypair,modifyDev,refcountDecAndTest,last,
                  branchCmp,AmbientM.branchCmp,IndexOwner.peerDeref,IndexOwner.peerWord,
                  word,unsupported,AmbientM.unsupported] at run
                cases run
              | some pid =>
                obtain ⟨u,final,next,actual,present⟩ :=
                  keypairPut_exact id false d k resident live (by simp [word]) g ambient device
                rw [run] at actual
                cases actual
                exact Or.inr ⟨id,d,k,rfl,rfl,resident,live,present⟩
            · obtain ⟨u,final,next,actual,present⟩ :=
                Config.keypairPut_retained id d k resident (by omega) g ambient device
              rw [run] at actual
              cases actual
              refine Or.inr ⟨id,d,k,rfl,rfl,resident,live,?_⟩
              simpa [releasedDevice,unhashKeypair,last,Config.withKeypair] using present

end Leanux.Proofs.WG.Index
