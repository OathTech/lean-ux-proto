import Leanux.Proofs.WG.Index.RetirementReleaseSource
import Leanux.Proofs.WG.Index.RetirementRetentionClaims
import Leanux.Proofs.WG.Queues.HolderRetirement

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise
open Queues.RxCredits Queues.RxCredits.DurableHolders

/-- Pay the actual head loan while retaining the remaining funded account,
stable RX state, hashed-slot coverage, owner coherence and retirement duties.
The retirement predicate already excludes the paid head occurrence: callers
must discharge that owner's hashed rows before dropping its last reservation.
Equal stamped owners may still occur in the remaining lists; counts, not set
membership, govern the payment. This is a same-normal-run composition only. -/
theorem peerPut_retirement_payment
    (original : DurableHolders) (cs : Ledger) (paid : Owner)
    (retired loans : Reservations) (w v : WGWorld) (a b : Ambient)
    (configured : ConfiguredIdentity.Inv w) (base : BaseCoherence.Inv w)
    (account : DuringWork original cs (paid :: (retired ++ loans)) w)
    (covered : ∀ d, w.dev = some d → HashSlotCoverage d)
    (coherent : ∀ d, w.dev = some d → HashedOwnersCoherent d)
    (reserved : ∀ d, w.dev = some d → DeadHashedReserved retired d)
    (run : ((peerPut (some paid.slot)).run w).run a = .ok (((),v),b)) :
    DuringWork original cs (retired ++ loans) v ∧
      View.HashSlotsSafe (Campaign2.snapshot v b) ∧
      View.OwnerCoherentSafe (Campaign2.snapshot v b) ∧
      View.RetirementSafe retired (Campaign2.snapshot v b) := by
  have paidAccount := DurableHolders.work_payment_normal account a b run
  obtain ⟨holders,_,funded,_⟩ := account
  have charged : 0 < demand cs (holders.owners ++ (paid :: (retired ++ loans))) paid := by
    simp only [demand,List.count_append,List.count_cons_self]
    omega
  obtain ⟨p,found,bound⟩ := protected_resident funded.carriers.funded charged
  obtain ⟨d,device,epoch,resident,stamp⟩ := resident_fields found
  have positive : 0 < p.refcount := by omega
  have paidAt : paid = ⟨d.ifindex,paid.slot,p.internalId⟩ := by
    cases paid
    simp only [Owner.mk.injEq]
    exact ⟨epoch.symm,True.intro,stamp.symm⟩
  have actualFunded : holders.Funded cs
      (⟨d.ifindex,paid.slot,p.internalId⟩ :: (retired ++ loans)) w := by
    rw [← paidAt]
    exact funded
  have roots : DeadHashedReserved (retired ++ loans) d := by
    intro entry member kid key pid peer owner keyFound keyPeer peerFound dead
    exact List.mem_append.mpr (Or.inl
      (reserved d device entry member kid key pid peer owner keyFound keyPeer peerFound dead))
  obtain ⟨present,coverage,coherence⟩ := peerPut_funded_hashSlots
    w v a b () configured base actualFunded device resident
      (coherent d device) (covered d device) roots run
  refine ⟨paidAccount,?_,?_,?_⟩
  · intro actual found
    change v.dev = some actual at found
    rw [present] at found
    cases found
    exact coverage
  · intro actual found
    change v.dev = some actual at found
    rw [present] at found
    cases found
    exact coherence
  · exact peerPut_retirement retired paid.slot d p resident positive
      w a () v b ⟨device,reserved⟩ run

end Leanux.Proofs.WG.Index
