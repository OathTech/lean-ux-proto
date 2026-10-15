import Leanux.Proofs.WG.TimerDiscipline.InitiationPreservationFrames
import Leanux.Proofs.WG.Index.PeerRelease

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

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

end Leanux.Proofs.WG.TimerDiscipline
