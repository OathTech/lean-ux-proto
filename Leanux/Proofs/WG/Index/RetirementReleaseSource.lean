import Leanux.Proofs.WG.Index.RetirementReleaseEffects
import Leanux.Proofs.WG.Index.HashSlotReleaseClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceReleaseClaims
import Leanux.Proofs.WG.Index.FundedBaseSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise
open Queues.RxCredits Queues.RxCredits.DurableHolders

/-- Extract the exact device effect from the existing all-outcome release
contract. The original queue/timer refusals are not assumed away. -/
theorem peerPut_normal_device (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (w out : WGWorld) (ambient after : Ambient) (result : Unit)
    (device : w.dev = some d)
    (run : (((peerPut (some pid)).run w).run ambient) = .ok ((result,out),after)) :
    out.dev = some (releasedPeerDevice d pid p) := by
  have exactOutcome := peerPut_exact pid d p resident live w ambient device
  change (match peerReleaseRefusal pid p with
    | some stop => Campaign2.observeResult (((peerPut (some pid)).run w).run ambient) = .error stop
    | none => ∃ final,
        Campaign2.observeResult (((peerPut (some pid)).run w).run ambient) = .ok ((),final) ∧
        final.wg.device = some (releasedPeerDevice d pid p)) at exactOutcome
  rw [run] at exactOutcome
  cases refusal : peerReleaseRefusal pid p with
  | some stop =>
    simp [refusal,Campaign2.observeResult,Except.map] at exactOutcome
  | none =>
    simp only [refusal,Campaign2.observeResult,Except.map,Except.ok.injEq,
      Prod.mk.injEq] at exactOutcome
    obtain ⟨final,⟨_,equal⟩,present⟩ := exactOutcome
    subst final
    exact present

/-- A native source composition: the paid loan is the caller's actual stamped
resident. Funding and retirement establish detachment before the actual put;
no final-state predicate or initialized reachability is supplied. -/
theorem peerPut_funded_hashSlots
    {holders : DurableHolders} {cs : Ledger} {retired : Reservations}
    {pid : PeerId} {d : Device} {p : Peer}
    (w out : WGWorld) (ambient after : Ambient) (result : Unit)
    (configured : ConfiguredIdentity.Inv w) (base : BaseCoherence.Inv w)
    (funded : holders.Funded cs (⟨d.ifindex,pid,p.internalId⟩ :: retired) w)
    (device : w.dev = some d) (resident : d.peers[pid]? = some p)
    (coherent : HashedOwnersCoherent d) (covered : HashSlotCoverage d)
    (reserved : DeadHashedReserved retired d)
    (run : (((peerPut (some pid)).run w).run ambient) = .ok ((result,out),after)) :
    out.dev = some (releasedPeerDevice d pid p) ∧
      HashSlotCoverage (releasedPeerDevice d pid p) ∧
      HashedOwnersCoherent (releasedPeerDevice d pid p) := by
  have positive := paid_loan_positive funded device resident
  have detached := funded_lastOwnerDetached configured base funded device resident coherent reserved
  refine ⟨peerPut_normal_device pid d p resident positive w out ambient after result device run,
    releasedPeer_hashSlotCoverage_detached d pid p resident detached covered,?_⟩
  by_cases last : p.refcount = 1
  · exact (lastPeerRelease_coherent_iff d pid p last coherent).mpr (detached last)
  · exact nonlastPeerRelease_coherent d pid p resident (by omega) coherent

end Leanux.Proofs.WG.Index
