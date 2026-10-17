import Leanux.Proofs.WG.Index.NewlinkFrames
import Leanux.Proofs.WG.Index.PeerReleaseClaims

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Table safety on every normal release, including removal of the last reference. -/
theorem peerPut_tables (peer : Option PeerId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ peerPut peer
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  cases peer with
  | none =>
    simp [peerPut, branch, AmbientM.branch] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact pre
  | some pid =>
    cases device : g.dev with
    | none =>
      simp [peerPut, branch, AmbientM.branch, requireNotPending, getPeer, getDev,
        device, invariant, AmbientM.invariant] at run
      cases run
    | some d =>
      cases resident : d.peers[pid]? with
      | none =>
        simp [peerPut, branch, AmbientM.branch, requireNotPending, getPeer, getDev,
          device, resident, invariant, AmbientM.invariant] at run
        cases run
      | some p =>
        by_cases zero : p.refcount = 0
        · simp [peerPut, branch, AmbientM.branch, requireNotPending, getPeer, getDev,
            device, resident, zero, refcountDecAndTest, branchCmp, AmbientM.branchCmp,
            invariant, AmbientM.invariant] at run
          cases run
        · have live : 0 < p.refcount := by omega
          have effect := peerPut_exact pid d p resident live g ambient device
          change (match peerReleaseRefusal pid p with
            | some stop => Campaign2.observeResult (((peerPut (some pid)).run g).run ambient) = .error stop
            | none => ∃ s, Campaign2.observeResult (((peerPut (some pid)).run g).run ambient) =
              .ok ((), s) ∧ s.wg.device = some (releasedPeerDevice d pid p)) at effect
          rw [run] at effect
          cases refused : peerReleaseRefusal pid p with
          | some stop => simp [refused, Campaign2.observeResult, Except.map] at effect
          | none =>
            simp only [refused, Campaign2.observeResult, Except.map] at effect
            obtain ⟨s, equality, actual⟩ := effect
            cases equality
            intro out found
            change final.dev = some (releasedPeerDevice d pid p) at actual
            rw [found] at actual
            cases actual
            have safe := pre d device
            exact ⟨releasedPeer_indices pid d p safe.1, releasedPeer_owners pid d p safe.2.1,
              releasedPeer_owners_bounded pid d p safe.2.2⟩

end Leanux.Proofs.WG.Index
