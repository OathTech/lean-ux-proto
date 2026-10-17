import Leanux.Proofs.WG.Index.OwnerCoherenceModel
import Leanux.Proofs.WG.Index.PeerRelease

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

/-- A locally coherent hashed keypair may name a last-reference peer. Actual
normal final release then removes the peer but retains the hashed keypair.
This is a local-state witness, without a reachability claim. -/
theorem peerPut_ownerCoherentSafe_counterexample :
    ∃ d : Device, HashedOwnersCoherent d ∧
      Campaign2.Observes (peerPut (some 0)) (fun s => s.wg.device = some d)
        (fun _ out => ∃ final, out = .ok ((), final) ∧ ¬ View.OwnerCoherentSafe final) := by
  let p : Peer := {
    remoteStatic := []
    presharedKey := []
    precomputedStaticStatic := []
    internalId := 0}
  let k : Keypair := {peer := some 0}
  let e : IndexEntry := {index := 7, owner := .keypair 0}
  let d : Device := {
    ifindex := 0
    ifname := "wg0"
    peers := ({} : Std.TreeMap PeerId Peer).insert 0 p,
    keypairs := ({} : Std.TreeMap KeypairId Keypair).insert 0 k,
    indexTable := [e], nextKeypairId := 1}
  have coherent : HashedOwnersCoherent d := by
    intro entry member
    have same : entry = e := by simpa [d] using member
    subst entry
    refine ⟨0, p, ?_, ?_, ?_, ?_⟩
    · simp [ownerWord, e, d, k]
    · simp [d]
    · decide
    · exact ⟨k, by simp [d], by decide⟩
  have resident : d.peers[0]? = some p := by simp [d]
  have live : 0 < p.refcount := by decide
  refine ⟨d, coherent, ?_⟩
  intro g ambient device
  have outcome := peerPut_exact 0 d p resident live g ambient device
  simp only [p, PeerTimer.all, Peer.timerPending, Peer.timer, Peer.wheel] at outcome
  simp at outcome
  obtain ⟨final, run, result⟩ := outcome
  refine ⟨final, run, ?_⟩
  intro safe
  have bad := safe (releasedPeerDevice d 0 p) result e (by
    simp [releasedPeerDevice, removeOwner, d, p, e])
  obtain ⟨pid, peer, word, found, positive, rest⟩ := bad
  have missing : (releasedPeerDevice d 0 p).peers[pid]? = none := by
    simp [releasedPeerDevice, d, p]
  rw [missing] at found
  cases found

end Leanux.Proofs.WG.Index
