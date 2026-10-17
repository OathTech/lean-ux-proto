import Leanux.Proofs.WG.TimerDiscipline.SendWorkerFrame
import Leanux.Proofs.WG.Index.PeerRelease
import Leanux.Proofs.WG.Index.PeerReleaseEffects

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem retained_peerPut_workerView (pid : PeerId) (identity attempts refs : Nat)
    (retained : 1 < refs) :
    Ensures (peerPut (some pid)) (fun w => workerAt w pid = some (identity, attempts, refs))
      (fun _ w => workerAt w pid = some (identity, attempts, refs - 1)) := by
  intro g ambient result final after pre run
  cases result
  cases hd : g.dev with
  | none => simp [workerAt, peerAt, hd] at pre
  | some d =>
    cases hp : d.peers[pid]? with
    | none => simp [workerAt, peerAt, hd, hp] at pre
    | some p =>
      have hv : workerView p = (identity, attempts, refs) := by
        simpa [workerAt, peerAt, hd, hp] using pre
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
      simp only [workerAt, peerAt, device, Option.bind_some, peer, Option.map_some]
      simp only [workerView, Option.some.injEq, Prod.mk.injEq] at hv ⊢
      exact ⟨hv.1, hv.2.1, by rw [hr]⟩

theorem handshakeSendWorker_workerView (pid : PeerId) (identity attempts refs : Nat)
    (retained : 1 < refs) :
    Ensures (handshakeSendWorker pid) (fun w => workerAt w pid = some (identity, attempts, refs))
      (fun _ w => workerAt w pid = some (identity, attempts, refs - 1)) := by
  unfold handshakeSendWorker
  exact ensures_bind _ _ (sendHandshakeInitiation_workerView pid (identity, attempts, refs))
    (fun _ => retained_peerPut_workerView pid identity attempts refs retained)

end Leanux.Proofs.WG.TimerDiscipline
