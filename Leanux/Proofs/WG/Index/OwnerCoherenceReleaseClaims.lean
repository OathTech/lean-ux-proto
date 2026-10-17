import Leanux.Proofs.WG.Index.OwnerCoherenceReleaseFrames
import Leanux.Proofs.WG.Index.OwnerCoherenceDecrementFrames
import Leanux.Proofs.WG.Index.PeerRelease
import Leanux.Proofs.WG.Index.PeerReleaseOutcomeModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

/-- Actual normal peer release preserves local owner coherence when the final
release's retained hashed owners do not name the released peer. Detachment is
an explicit obligation; it is not asserted to follow from reachability. Queue
and timer refusal paths remain outside this normal-return postcondition. -/
theorem peerPut_owner_coherent (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (detached : p.refcount = 1 → ∀ e ∈ d.indexTable,
      e.owner ≠ .handshake pid → ownerWord d e.owner ≠ some (some pid)) :
    Campaign2.Ensures (peerPut (some pid))
      (fun s => s.wg.device = some d ∧ View.OwnerCoherentSafe s)
      (fun _ s => View.OwnerCoherentSafe s) := by
  intro g ambient value final after pre run
  have exactOutcome := peerPut_exact pid d p resident live g ambient pre.1
  change (match peerReleaseRefusal pid p with
    | some stop => Campaign2.observeResult (((peerPut (some pid)).run g).run ambient) = .error stop
    | none => ∃ out,
        Campaign2.observeResult (((peerPut (some pid)).run g).run ambient) = .ok ((), out) ∧
        out.wg.device = some (releasedPeerDevice d pid p)) at exactOutcome
  rw [run] at exactOutcome
  cases refusal : peerReleaseRefusal pid p with
  | some stop =>
    simp [refusal, Campaign2.observeResult, Except.map] at exactOutcome
  | none =>
    simp only [refusal, Campaign2.observeResult, Except.map, Except.ok.injEq,
      Prod.mk.injEq] at exactOutcome
    obtain ⟨out, ⟨_, equal⟩, device⟩ := exactOutcome
    subst out
    have entry : HashedOwnersCoherent d := pre.2 d pre.1
    have preserved : HashedOwnersCoherent (releasedPeerDevice d pid p) := by
      by_cases last : p.refcount = 1
      · exact (lastPeerRelease_coherent_iff d pid p last entry).mpr (detached last)
      · exact nonlastPeerRelease_coherent d pid p resident (by omega) entry
    intro observed present
    rw [device] at present
    cases present
    exact preserved

end Leanux.Proofs.WG.Index
