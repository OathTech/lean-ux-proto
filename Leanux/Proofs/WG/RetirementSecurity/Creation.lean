import Leanux.Proofs.WG.RetirementSecurity.Acquire
import Leanux.Proofs.WG.Origins.SessionMaterial

/-! Actual successful creation supplies the initial one-reference loan.
The existing allocation invariant supplies slot vacancy; the credit account
does not silently discard overwritten references on arbitrary raw inputs. -/
namespace Leanux.Proofs.WG.RetirementSecurity.Credits
open Leanux Leanux.WG Leanux.Proofs.WG.Lifetimes

theorem initial (net bare : Bool) : Exact [] (Runner.initialWG net bare) := by
  intro allocation
  cases net <;> cases bare <;> simp [balance,keyAt,Runner.initialWG]

theorem Exact.create (account : Exact credits w) (allocation : AllocationInv history w)
    (word : Option PeerId) (id : KeypairId) (a b : Ambient)
    (run : ((keypairCreate word).run w).run a = .ok ((some id,v),b)) :
    Exact (⟨id,w.keypairCounter + 1⟩ :: credits) v := by
  obtain ⟨d,device,rfl,rfl⟩ := Origins.create_some word w v id a b run
  have vacant := allocation.key_vacant device
  intro other
  have before := account other
  by_cases same : other = (⟨d.nextKeypairId,w.keypairCounter + 1⟩ : Allocation)
  · subst other
    simp [balance,keyAt,device,vacant] at before
    simp [balance,keyAt,keyAllocationWorld,keyAllocationDevice,before]
  · have count : ((⟨d.nextKeypairId,w.keypairCounter + 1⟩ : Allocation) :: credits).count other =
        credits.count other := by simp [Ne.symm same]
    rw [count]
    by_cases slot : other.slot = d.nextKeypairId
    · have stamp : w.keypairCounter + 1 ≠ other.stamp := by
        intro equal
        apply same
        cases other
        simp_all
      simpa [balance,keyAt,device,vacant,keyAllocationWorld,keyAllocationDevice,slot,stamp] using before
    · simpa [balance,keyAt,device,keyAllocationWorld,keyAllocationDevice,
        Std.TreeMap.getElem?_insert,Ne.symm slot] using before

theorem Exact.put_last (account : Exact (allocation :: credits) w)
    (last : allocation ∉ credits) (now : Bool) (a b : Ambient)
    (run : ((keypairPut (some allocation.slot) now).run w).run a = .ok (((),v),b)) :
    keyAt v allocation.slot = none ∧ Unpublished allocation.slot v := by
  obtain ⟨k,found,stamp,_⟩ := account.resident (allocation := allocation) (by simp)
  have count := account allocation
  have one : k.refcount = 1 := by
    simpa [balance,found,stamp,List.count_eq_zero.mpr last] using count.symm
  cases device : w.dev with
  | none => simp [keyAt,device] at found
  | some d =>
    have resident : d.keypairs[allocation.slot]? = some k := by simpa [keyAt,device] using found
    have effect := put_effect allocation.slot now w v a b d k device resident run
    exact ⟨effect.final one,effect.unpublished (Or.inr one)⟩

theorem Exact.put_outstanding (account : Exact (allocation :: credits) w)
    (outstanding : allocation ∈ credits) (now : Bool) (a b : Ambient)
    (run : ((keypairPut (some allocation.slot) now).run w).run a = .ok (((),v),b)) :
    ∃ k, keyAt w allocation.slot = some k ∧ k.internalId = allocation.stamp ∧
      keyAt v allocation.slot = some {k with refcount := k.refcount - 1} := by
  obtain ⟨k,found,stamp,_⟩ := account.resident (allocation := allocation) (by simp)
  have count := account allocation
  have positive : 0 < credits.count allocation := List.count_pos_iff.mpr outstanding
  have more : 1 < k.refcount := by
    simp only [List.count_cons_self,balance,found,stamp,↓reduceIte] at count
    omega
  cases device : w.dev with
  | none => simp [keyAt,device] at found
  | some d =>
    have resident : d.keypairs[allocation.slot]? = some k := by simpa [keyAt,device] using found
    exact ⟨k,found,stamp,(put_effect allocation.slot now w v a b d k device resident run).nonfinal more⟩

end Leanux.Proofs.WG.RetirementSecurity.Credits
