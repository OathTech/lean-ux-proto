import Leanux.Proofs.WG.RetirementSecurity.CarrierFrames
import Leanux.Proofs.WG.RetirementSecurity.Acquire

/-! Native temporary-reference acquisition and payment preserve an exact
account whose durable side is the concrete state projection. In particular,
the remaining real holders, rather than an assumed count inequality, prevent
release from deleting their allocation. Whole-run transport through holder
publication/removal remains separate. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

theorem durable_resident {loans : List KeyLoan}
    (account : Credits.Exact (loans.map (·.allocation) ++ temporary) w)
    (loan : KeyLoan) (member : loan ∈ loans) :
    ∃ k, keyAt w loan.allocation.slot = some k ∧ k.internalId = loan.allocation.stamp := by
  obtain ⟨k,found,stamp,_⟩ := account.resident
    (List.mem_append_left temporary (List.mem_map_of_mem member))
  exact ⟨k,found,stamp⟩

theorem HolderAccount.put (account : HolderAccount (paid :: temporary) w)
    (now : Bool) (a b : Ambient)
    (run : ((keypairPut (some paid.slot) now).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary v := by
  obtain ⟨loans,projected,credits⟩ := account
  have paidAccount := (credits.perm List.perm_middle).put now a b run
  have shape := (ProjectedAction.iff_run_ambient _ _ _).mp
    (put_carriers (some paid.slot) now) w a () v b run
  exact ⟨loans,durableLoans_transport loans shape projected
    (durable_resident paidAccount),paidAccount⟩

theorem HolderAccount.get (account : HolderAccount temporary w)
    (id : KeypairId) (k : Keypair) (found : keyAt w id = some k) (a b : Ambient)
    (run : ((keypairGet (some id)).run w).run a = .ok ((some id,v),b)) :
    HolderAccount (⟨id,k.internalId⟩ :: temporary) v := by
  obtain ⟨loans,projected,credits⟩ := account
  have acquired := (credits.get id k found a b run).perm List.perm_middle.symm
  have shape := (ProjectedAction.iff_run_ambient _ _ _).mp
    (get_carriers (some id)) w a (some id) v b run
  exact ⟨loans,durableLoans_transport loans shape projected
    (durable_resident acquired),acquired⟩

theorem HolderAccount.put_last (account : HolderAccount (paid :: temporary) w)
    (last : ∀ loans, durableLoans w = some loans →
      paid ∉ loans.map (·.allocation) ++ temporary)
    (now : Bool) (a b : Ambient)
    (run : ((keypairPut (some paid.slot) now).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary v ∧ keyAt v paid.slot = none ∧ Unpublished paid.slot v := by
  obtain ⟨loans,projected,credits⟩ := account
  exact ⟨HolderAccount.put ⟨loans,projected,credits⟩ now a b run,
    (credits.perm List.perm_middle).put_last (last loans projected) now a b run⟩

theorem HolderAccount.put_durable (account : HolderAccount (paid :: temporary) w)
    (projected : durableLoans w = some loans) (loan : KeyLoan) (member : loan ∈ loans)
    (same : loan.allocation = paid) (now : Bool) (a b : Ambient)
    (run : ((keypairPut (some paid.slot) now).run w).run a = .ok (((),v),b)) :
    ∃ k, keyAt w paid.slot = some k ∧ k.internalId = paid.stamp ∧
      keyAt v paid.slot = some {k with refcount := k.refcount - 1} := by
  obtain ⟨actual,actualProjected,credits⟩ := account
  have sameLoans : actual = loans := Option.some.inj (actualProjected.symm.trans projected)
  subst actual
  apply (credits.perm List.perm_middle).put_outstanding _ now a b run
  exact List.mem_append_left temporary (same ▸ List.mem_map_of_mem member)

end Leanux.Proofs.WG.RetirementSecurity
