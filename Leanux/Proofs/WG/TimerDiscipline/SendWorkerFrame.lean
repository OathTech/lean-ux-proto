import Leanux.Proofs.WG.TimerDiscipline.InitiationPreservation
import Leanux.Proofs.WG.Index.PeerRelease

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def initiationWorkerView (v : InitiationView) : WorkerView := (v.1, v.2.1, v.2.2.1)

theorem workerAt_of_initiationAt (w : World) (pid : PeerId) (v : InitiationView)
    (pre : initiationAt w pid = some v) : workerAt w pid = some (initiationWorkerView v) := by
  have h := congrArg (Option.map initiationWorkerView) pre
  simpa [initiationAt, workerAt, initiationView, workerView, initiationWorkerView,
    Option.map_map, Function.comp_def] using h

theorem sendHandshakeInitiation_workerView (pid : PeerId) (v : WorkerView) :
    Ensures (sendHandshakeInitiation pid) (fun w => workerAt w pid = some v)
      (fun _ w => workerAt w pid = some v) := by
  intro w result final pre run
  cases result
  cases hd : w.k.wg with
  | none => simp [workerAt, peerAt, hd] at pre
  | some d =>
    cases hp : d.peers[pid]? with
    | none => simp [workerAt, peerAt, hd, hp] at pre
    | some p =>
      have hv : workerView p = v := by simpa [workerAt, peerAt, hd, hp] using pre
      obtain ⟨reached, middle, hprefix, finish⟩ := sendInitiation_arm_execution pid w final run
      have hmid := (ensures_iff _ _ _).mpr (initiationArmPrefix_view pid (initiationView p))
        w reached middle (by simp [initiationAt, peerAt, hd, hp]) hprefix
      have hm := workerAt_of_initiationAt middle pid (initiationView p) hmid
      change workerAt middle pid = some (workerView p) at hm
      rw [hv] at hm
      cases reached with
      | false =>
        change final = middle at finish
        rw [finish]
        exact hm
      | true =>
        exact (ensures_iff _ _ _).mpr (timersHandshakeInitiated_workerView pid v)
          middle () final hm finish

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
