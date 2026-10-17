import Leanux.Proofs.WG.TimerDiscipline.InitiationPreservationFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem workerAt_of_initiationAt (w : WGWorld) (pid : PeerId) (v : InitiationView)
    (pre : initiationAt w pid = some v) : workerAt w pid = some (initiationWorkerView v) := by
  have h := congrArg (Option.map initiationWorkerView) pre
  simpa [initiationAt, workerAt, initiationView, workerView, initiationWorkerView,
    Option.map_map, Function.comp_def] using h

theorem sendHandshakeInitiation_workerView (pid : PeerId) (v : WorkerView) :
    Ensures (sendHandshakeInitiation pid) (fun w => workerAt w pid = some v)
      (fun _ w => workerAt w pid = some v) := by
  intro g ambient result final after pre run
  cases hd : g.dev with
  | none => simp [workerAt, peerAt, hd] at pre
  | some d =>
    cases hp : d.peers[pid]? with
    | none => simp [workerAt, peerAt, hd, hp] at pre
    | some p =>
      have hv : workerView p = v := by simpa [workerAt, peerAt, hd, hp] using pre
      rw [sendInitiation_arm_source] at run
      have prefixFrame : Ensures (initiationArmPrefix pid)
          (fun g => initiationAt g pid = some (initiationView p))
          (fun _ g => workerAt g pid = some v) := by
        intro initial inputs reached middle remaining pre prefixRun
        have preserved := (ensures_iff _ _ _).mpr (initiationArmPrefix_view pid (initiationView p))
          initial inputs reached middle remaining pre prefixRun
        have worker := workerAt_of_initiationAt middle pid (initiationView p) preserved
        change workerAt middle pid = some (workerView p) at worker
        simpa [hv] using worker
      have tail (reached : Bool) :
          Ensures (if reached then timersHandshakeInitiated pid else pure ())
            (fun g => workerAt g pid = some v) (fun _ g => workerAt g pid = some v) := by
        cases reached with
        | false => intro g ambient result final after pre run; cases run; exact pre
        | true => exact (ensures_iff _ _ _).mpr (timersHandshakeInitiated_workerView pid v)
      exact ensures_bind _ _ prefixFrame tail g ambient result final after
        (by simp [initiationAt, peerAt, hd, hp]) run

end Leanux.Proofs.WG.TimerDiscipline
