import Leanux.Proofs.WG.Progress.FlushBaseFrames
import Leanux.Proofs.WG.TimerDiscipline.WorkStateFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Proofs.WG.Noise TimerDiscipline Std.Do

theorem sendHandshakeInitiation_flushQueues (pid : PeerId) (queues : WorkQueues) :
    ⦃fun w => ⌜flushQueueAt w = some queues⌝⦄ sendHandshakeInitiation pid
      ⦃⇓? _ w => ⌜flushQueueAt w = some queues⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w result final pre run
  cases hd : w.k.wg with
  | none => simp [flushQueueAt, flushQueueKernel, hd] at pre
  | some d =>
    cases hp : d.peers[pid]? with
    | none =>
      have failed : (getPeer pid).run w = .error (.invariant s!"dangling peer {pid}") := by
        simp [getPeer, getDev, getK, invariant, hd, hp]
        rfl
      change ((getPeer pid).run w >>= _) = .ok (result, final) at run
      rw [failed] at run
      cases run
    | some p =>
      have h := sendHandshakeInitiation_queueWorkView pid queues p.handshakePending
        w result final (by
          apply Prod.ext
          · exact pre
          · simp [queueWorkAt, queueWorkKernel, hd, hp]) run
      exact congrArg Prod.fst h

theorem handshakeSendWorker_flushQueues (pid : PeerId) (queues : WorkQueues) :
    ⦃fun w => ⌜flushQueueAt w = some queues⌝⦄ handshakeSendWorker pid
      ⦃⇓? _ w => ⌜flushQueueAt w = some queues⌝⦄ := by
  have hs := sendHandshakeInitiation_flushQueues pid queues
  have hp := peerPut_spec_queue_variant (some pid) queues
  mvcgen [handshakeSendWorker, hs, hp]

end Leanux.Proofs.WG.Progress
