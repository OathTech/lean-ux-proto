import Leanux.Proofs.WG.Index.PeerRelease
import Leanux.Proofs.WG.Index.PeerReleaseEffects
import Leanux.Proofs.WG.Index.PeerReleaseOutcomeModel

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

namespace ReleaseClaims
/-- The original resident/live domain has an exact refusal or normal return.
On return, all original table, peer, drop-accounting and uniqueness effects
hold. Refusal exposes no post-state; reference safety elsewhere is not claimed. -/
theorem original_peer_release (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (indices : UniqueIndices d.indexTable) (owners : UniqueOwners d.indexTable) :
    Campaign2.Observes (peerPut (some pid)) (fun w => w.wg.device = some d)
      (fun _ out =>
        match peerReleaseRefusal pid p with
        | some stop => out = .error stop
        | none => ∃ w, out = .ok ((), w) ∧
        let final := releasedPeerDevice d pid p
        w.wg.device = some final ∧
        final.indexTable = (if p.refcount = 1 then removeOwner (.handshake pid) d.indexTable else d.indexTable) ∧
        final.peers[pid]? = (if p.refcount = 1 then none else some { p with refcount := p.refcount - 1 }) ∧
        (∀ other : PeerId, pid ≠ other → final.peers[other]? = d.peers[other]?) ∧
        final.txDropped = d.txDropped + (if p.refcount = 1 then p.staged.length else 0) ∧
        UniqueIndices final.indexTable ∧ UniqueOwners final.indexTable) := by
  intro g ambient pre
  have effect := peerPut_exact pid d p resident live g ambient pre
  change (match peerReleaseRefusal pid p with
    | some stop => Campaign2.observeResult (((peerPut (some pid)).run g).run ambient) = .error stop
    | none => ∃ w, Campaign2.observeResult (((peerPut (some pid)).run g).run ambient) =
        .ok ((), w) ∧ w.wg.device = some (releasedPeerDevice d pid p)) at effect
  cases refused : peerReleaseRefusal pid p with
  | some stop => simpa only [refused] using effect
  | none =>
    rw [refused] at effect
    obtain ⟨final, run, device⟩ := effect
    exact ⟨final, run, device, releasedPeer_table pid d p, releasedPeer_peer pid d p,
      fun other different => releasedPeer_other pid other d p different, releasedPeer_dropped pid d p,
      releasedPeer_indices pid d p indices, releasedPeer_owners pid d p owners⟩

/-- Exact refusal or normal preservation of the original keypair store, cursor
and allocation bounds. No whole-driver initialization or preservation is claimed. -/
theorem original_peer_release_allocation_bounds (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (owners : KeypairOwnersBounded d) (store : KeypairStoreBounded d) :
    Campaign2.Observes (peerPut (some pid)) (fun w => w.wg.device = some d)
      (fun _ out =>
        match peerReleaseRefusal pid p with
        | some stop => out = .error stop
        | none => ∃ w, out = .ok ((), w) ∧
        let final := releasedPeerDevice d pid p
        w.wg.device = some final ∧ final.keypairs = d.keypairs ∧ final.nextKeypairId = d.nextKeypairId ∧
        KeypairOwnersBounded final ∧ KeypairStoreBounded final) := by
  intro g ambient pre
  have effect := peerPut_exact pid d p resident live g ambient pre
  change (match peerReleaseRefusal pid p with
    | some stop => Campaign2.observeResult (((peerPut (some pid)).run g).run ambient) = .error stop
    | none => ∃ w, Campaign2.observeResult (((peerPut (some pid)).run g).run ambient) =
        .ok ((), w) ∧ w.wg.device = some (releasedPeerDevice d pid p)) at effect
  cases refused : peerReleaseRefusal pid p with
  | some stop => simpa only [refused] using effect
  | none =>
    rw [refused] at effect
    obtain ⟨final, run, device⟩ := effect
    exact ⟨final, run, device, releasedPeer_keypairs pid d p, releasedPeer_next pid d p,
      releasedPeer_owners_bounded pid d p owners, releasedPeer_store_bounded pid d p store⟩

end ReleaseClaims
end Leanux.Proofs.WG.Index
