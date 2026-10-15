import Leanux.Proofs.WG.TimerDiscipline.SendWorkerFrame
set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem retained_peerPut_workerView (pid : PeerId) (identity attempts refs : Nat)
    (retained : 1 < refs) :
    Ensures (peerPut (some pid)) (fun w => workerAt w pid = some (identity, attempts, refs))
      (fun _ w => workerAt w pid = some (identity, attempts, refs - 1)) := by
  intro w result final pre run
  cases hd : w.k.wg with
  | none => simp [workerAt, peerAt, hd] at pre
  | some d =>
    cases hp : d.peers[pid]? with
    | none => simp [workerAt, peerAt, hd, hp] at pre
    | some p =>
      have hv : workerView p = (identity, attempts, refs) := by
        simpa [workerAt, peerAt, hd, hp] using pre
      have hr : p.refcount = refs := congrArg (fun x => x.2.2) hv
      have last : p.refcount ≠ 1 := by omega
      obtain ⟨out, after, execution, device⟩ := Index.peerPut_exact pid d p hp (by omega) w hd
      rw [run] at execution
      cases execution
      have peer := Index.releasedPeer_peer pid d p
      rw [if_neg last] at peer
      simp only [workerAt, peerAt, device, Option.bind_some, peer, Option.map_some]
      simp only [workerView, Option.some.injEq, Prod.mk.injEq] at hv ⊢
      exact ⟨hv.1, hv.2.1, by rw [hr]⟩

theorem handshakeSendWorker_workerView (pid : PeerId) (identity attempts refs : Nat)
    (retained : 1 < refs) :
    Ensures (handshakeSendWorker pid) (fun w => workerAt w pid = some (identity, attempts, refs))
      (fun _ w => workerAt w pid = some (identity, attempts, refs - 1)) := by
  rw [ensures_iff]
  have hs := (ensures_iff _ _ _).mp (sendHandshakeInitiation_workerView pid (identity, attempts, refs))
  have hp := (ensures_iff _ _ _).mp (retained_peerPut_workerView pid identity attempts refs retained)
  mvcgen [handshakeSendWorker, hs, hp]

end Leanux.Proofs.WG.TimerDiscipline
