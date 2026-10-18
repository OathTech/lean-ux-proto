import Leanux.Proofs.WG.RetirementSecurity.HolderEntry
import Leanux.Proofs.WG.RetirementSecurity.HolderPayments

/-! The current slot's real durable occurrence funds the original staged
key acquisition. A successful normal call cannot refuse a resident positive
count; saturation remains the source's explicit Stop. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG

theorem get_positive_result {id : KeypairId} (found : keyAt w id = some k) (positive : 0 < k.refcount)
    (a b : Ambient)
    (run : ((keypairGet (some id)).run w).run a = .ok ((result,v),b)) : result = some id := by
  cases device : w.dev with
  | none => simp [keyAt,device] at found
  | some d =>
    have resident : d.keypairs[id]? = some k := by simpa [keyAt,device] using found
    have zero : k.refcount ≠ 0 := by omega
    by_cases overflow : k.refcount + 1 ≥ 2 ^ 31
    all_goals have wrap : (2147483647 ≤ k.refcount) ↔ (k.refcount + 1 ≥ 2 ^ 31) := by omega
    all_goals simp [keypairGet,refcountIncNotZero,branch,branchCmp,getKeypair,getDev,
      device,resident,zero,overflow,wrap,setKeypair,modifyDev,unsupported,
      AmbientM.branch,AmbientM.branchCmp,AmbientM.unsupported,
      StateT.run_bind,StateT.run_get,StateT.run_pure] at run
    all_goals obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
    rfl

theorem HolderAccount.current_get (account : HolderAccount temporary w)
    (found : peerAt w pid = some p) (a b : Ambient)
    (run : ((keypairGet p.keypairCurrent).run w).run a = .ok ((result,v),b)) :
    ∃ saved : Option Credits.Allocation,
      result = p.keypairCurrent ∧ saved.map (·.slot) = result ∧
      HolderAccount (saved.toList ++ temporary) v := by
  obtain ⟨slots,remaining,aligned,_,credits⟩ := account.peer_funding found
  have current := aligned.2.2
  cases saved : slots.current with
  | none =>
    have absent : p.keypairCurrent = none := by simpa [saved] using current.symm
    rw [absent] at run
    simp [keypairGet,branch,AmbientM.branch] at run
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
    exact ⟨none,absent.symm,rfl,account⟩
  | some allocation =>
    have slot : p.keypairCurrent = some allocation.slot := by simpa [saved] using current.symm
    obtain ⟨k,resident,stamp,positive⟩ := credits.resident (allocation := allocation)
      (by simp [SlotLoans.credits,saved])
    rw [slot] at run
    have resultSame := get_positive_result resident positive a b run
    subst result
    refine ⟨some allocation,slot.symm,rfl,?_⟩
    have acquired := account.get allocation.slot k resident a b run
    have sameAllocation : (⟨allocation.slot,k.internalId⟩ : Credits.Allocation) = allocation := by
      cases allocation
      simp_all
    simpa only [sameAllocation,Option.toList_some,List.singleton_append] using acquired

end Leanux.Proofs.WG.RetirementSecurity
