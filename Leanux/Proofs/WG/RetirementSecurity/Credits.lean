import Leanux.Proofs.WG.RetirementSecurity.Consequences

/-! Exact key-reference occurrence accounting. Each list occurrence denotes
one reference to a slot and its allocation stamp. This account is deliberately
separate from source-holder alignment: slots, RX packets, TX batches and
temporary locals still have to supply their actual occurrences. -/
namespace Leanux.Proofs.WG.RetirementSecurity.Credits
open Leanux Leanux.WG

structure Allocation where
  slot : KeypairId
  stamp : Nat
  deriving DecidableEq

abbrev Ledger := List Allocation

def balance (w : WGWorld) (allocation : Allocation) : Nat :=
  match keyAt w allocation.slot with
  | none => 0
  | some k => if k.internalId = allocation.stamp then k.refcount else 0

def Exact (credits : Ledger) (w : WGWorld) : Prop :=
  ∀ allocation, credits.count allocation = balance w allocation

theorem Exact.resident (account : Exact credits w) (held : allocation ∈ credits) :
    ∃ k, keyAt w allocation.slot = some k ∧ k.internalId = allocation.stamp ∧
      0 < k.refcount := by
  have positive : 0 < balance w allocation := by
    rw [←account allocation]
    exact List.count_pos_iff.mpr held
  unfold balance at positive
  cases found : keyAt w allocation.slot with
  | none => simp [found] at positive
  | some k =>
    by_cases stamp : k.internalId = allocation.stamp
    · exact ⟨k,rfl,stamp,by simpa [found,stamp] using positive⟩
    · simp [found,stamp] at positive

theorem Exact.absent (account : Exact credits w) (absent : keyAt w allocation.slot = none) :
    allocation ∉ credits := by
  intro held
  obtain ⟨k,found,_,_⟩ := account.resident held
  rw [absent] at found
  cases found

theorem Exact.perm (account : Exact credits w) (permutation : credits.Perm other) :
    Exact other w := fun allocation =>
  (permutation.count_eq allocation).symm.trans (account allocation)

/-- Pay an actual selected occurrence. Other references retain exact funding;
neither the reference count nor the selected allocation is assumed afterward. -/
theorem Exact.put (account : Exact (allocation :: credits) w)
    (now : Bool) (a b : Ambient)
    (run : ((keypairPut (some allocation.slot) now).run w).run a = .ok (((),v),b)) :
    Exact credits v := by
  obtain ⟨k,found,stamp,positive⟩ := account.resident (allocation := allocation) (by simp)
  cases device : w.dev with
  | none => simp [keyAt,device] at found
  | some d =>
    have resident : d.keypairs[allocation.slot]? = some k := by simpa [keyAt,device] using found
    have effect := put_effect allocation.slot now w v a b d k device resident run
    intro other
    have before := account other
    by_cases same : other = allocation
    · subst other
      simp only [List.count_cons_self] at before
      simp only [balance,found,stamp,↓reduceIte] at before
      by_cases final : k.refcount = 1
      · simp [balance,effect.selected,keyAfterPut,final]
        omega
      · simp only [balance,effect.selected,keyAfterPut,final,↓reduceIte,stamp]
        omega
    · have count : (allocation :: credits).count other = credits.count other := by
        simp [Ne.symm same]
      rw [count] at before
      by_cases slot : other.slot = allocation.slot
      · have different : k.internalId ≠ other.stamp := by
          intro equal
          apply same
          cases other
          cases allocation
          simp_all
        have oldZero : balance w other = 0 := by simp [balance,slot,found,different]
        have newZero : balance v other = 0 := by
          by_cases final : k.refcount = 1 <;>
            simp [balance,slot,effect.selected,keyAfterPut,final,different]
        exact before.trans (oldZero.trans newZero.symm)
      · have unchanged : balance v other = balance w other := by
          simp only [balance,effect.others other.slot slot]
        exact before.trans unchanged.symm

end Leanux.Proofs.WG.RetirementSecurity.Credits
