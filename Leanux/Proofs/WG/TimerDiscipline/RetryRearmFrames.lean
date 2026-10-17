import Leanux.Proofs.WG.TimerDiscipline.SendWorkerSource
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do
theorem retained_peerPut_workerView_retransmit_variant (pid : PeerId) (identity attempts refs : Nat)
    (expiry : Option UInt64) (retained : 1 < refs) :
    Campaign2.Ensures (peerPut (some pid))
      (fun s => workerObservation s pid = some (identity, attempts, refs) ∧
        (s.peerAt pid).map Peer.timerRetransmitHandshake = some expiry)
      (fun _ s => (s.peerAt pid).map Peer.timerRetransmitHandshake = some expiry) := by
  intro g ambient result final after pre run
  change workerAt g pid = some (identity, attempts, refs) ∧
    (peerAt g pid).map Peer.timerRetransmitHandshake = some expiry at pre
  cases result
  cases hd : g.dev with
  | none => simp [workerAt, peerAt, hd] at pre
  | some d =>
    cases hp : d.peers[pid]? with
    | none => simp [workerAt, peerAt, hd, hp] at pre
    | some p =>
      have hv : workerView p = (identity, attempts, refs) := by
        simpa [workerAt, peerAt, hd, hp] using pre.1
      have hr : p.refcount = refs := congrArg (fun x => x.2.2) hv
      have last : p.refcount ≠ 1 := by omega
      have effect := Index.peerPut_exact pid d p hp (by omega) g ambient hd
      simp only [last, ite_false] at effect
      change ∃ observed, Campaign2.observeResult _ = .ok ((), observed) ∧
        observed.wg.device = some (Index.releasedPeerDevice d pid p) at effect
      rw [run] at effect
      obtain ⟨observed, equality, device⟩ := effect
      have observedEq : Campaign2.snapshot final after = observed := by
        exact congrArg Prod.snd (Except.ok.inj equality)
      rw [← observedEq] at device
      change final.dev = some (Index.releasedPeerDevice d pid p) at device
      have peer := Index.releasedPeer_peer pid d p
      simp only [last, ite_false] at peer
      change (peerAt final pid).map Peer.timerRetransmitHandshake = some expiry
      simpa [peerAt, device, peer, Index.releasedPeerDevice, last, hd, hp] using pre.2

end Leanux.Proofs.WG.TimerDiscipline
