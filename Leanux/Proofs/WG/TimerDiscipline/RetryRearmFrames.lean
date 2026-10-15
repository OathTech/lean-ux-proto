import Leanux.Proofs.WG.TimerDiscipline.RetryRearmModel
import Leanux.Proofs.WG.TimerDiscipline.SendWorkerSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Local retransmit-expiry variant of retained_peerPut_workerView. The retained
reference condition excludes deletion; this helper only frames the timer field. -/
theorem retained_peerPut_workerView_retransmit_variant (pid : PeerId)
    (identity attempts refs : Nat) (expiry : Option UInt64) (retained : 1 < refs) :
    Ensures (peerPut (some pid))
      (fun w => workerAt w pid = some (identity, attempts, refs) ∧
        retransmitObservation (Campaign2.snapshot w) pid = some expiry)
      (fun _ w => retransmitObservation (Campaign2.snapshot w) pid = some expiry) := by
  intro w result final pre run
  cases hd : w.k.wg with
  | none => simp [workerAt, peerAt, hd] at pre
  | some d =>
    cases hp : d.peers[pid]? with
    | none => simp [workerAt, peerAt, hd, hp] at pre
    | some p =>
      have hv : workerView p = (identity, attempts, refs) := by
        simpa [workerAt, peerAt, hd, hp] using pre.1
      have hr : p.refcount = refs := congrArg (fun x => x.2.2) hv
      have last : p.refcount ≠ 1 := by omega
      obtain ⟨out, after, execution, device⟩ := Index.peerPut_exact pid d p hp (by omega) w hd
      rw [run] at execution
      cases execution
      have peer := Index.releasedPeer_peer pid d p
      rw [if_neg last] at peer
      simpa [retransmitObservation, Campaign2.snapshot, Campaign2.core, Campaign2.Snapshot.peerAt,
        device, peer, hd, hp] using pre.2

end Leanux.Proofs.WG.TimerDiscipline
