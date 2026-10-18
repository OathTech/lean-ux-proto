import Leanux.Proofs.WG.RetirementSecurity.Model

/-! Exact normal effects of the original keypair release. A normal-run premise
keeps NULL-owner and count-warning Stops explicit; no successful retirement is
inferred merely from a numerical count. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing

theorem put_effect (id : KeypairId) (now : Bool) (w v : WGWorld)
    (a b : Ambient) (d : Device) (k : Keypair)
    (device : w.dev = some d) (resident : d.keypairs[id]? = some k)
    (run : ((keypairPut (some id) now).run w).run a = .ok (((),v),b)) :
    PutEffect id now k w v := by
  cases now <;> cases owner : k.peer <;>
    by_cases zero : k.refcount = 0 <;> by_cases final : k.refcount = 1
  all_goals simp [keypairPut, IndexOwner.peerDeref, IndexOwner.peerWord,
    branch, branchCmp, getKeypair, getDev, device, resident, owner, zero, final,
    Nat.pos_iff_ne_zero, setKeypair, modifyDev, refcountDecAndTest, unsupported,
    indexRemove_eq, indexUnhash, liftM, monadLift, MonadLift.monadLift, liftIndex,
    AmbientM.branch, AmbientM.branchCmp, AmbientM.unsupported,
    StateT.run_bind, StateT.run_get, StateT.run_pure] at run
  all_goals obtain ⟨rfl,rfl⟩ := run
  all_goals constructor
  all_goals first
    | omega
    | rfl
    | (intro other different
       simp [keyAt,device,Std.TreeMap.getElem?_insert,Std.TreeMap.getElem?_erase,
         Ne.symm different])
    | (simp [keyAt,keyAfterPut,indexAt,withoutKeyIndex,peersAt,device,final,owner])

end Leanux.Proofs.WG.RetirementSecurity
