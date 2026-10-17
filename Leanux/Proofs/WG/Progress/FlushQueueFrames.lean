import Leanux.Proofs.WG.Progress.FlushBaseFrames
import Leanux.Proofs.WG.TimerDiscipline.WorkStateFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Proofs.WG.Noise TimerDiscipline Std.Do

theorem sendHandshakeInitiation_flushQueues (pid : PeerId) (queues : WorkQueues) :
    ⦃fun g => ⌜flushQueueAt g = some queues⌝⦄ sendHandshakeInitiation pid
      ⦃⇓? _ g => ⌜flushQueueAt g = some queues⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  cases hd : g.dev with
  | none => simp [flushQueueAt, flushQueueKernel, hd] at pre
  | some d =>
    cases hp : d.peers[pid]? with
    | none =>
      have failed : ((getPeer pid).run g).run ambient = .error (.invariant s!"dangling peer {pid}") := by
        simp [getPeer, getDev, invariant, AmbientM.invariant, hd, hp]
        rfl
      change (((getPeer pid).run g).run ambient >>= _) = .ok ((result, final), after) at run
      rw [failed] at run
      cases run
    | some p =>
      have h := sendHandshakeInitiation_queueWorkView pid queues p.handshakePending
        g ambient result final after (by
          apply Prod.ext
          · exact pre
          · simp [queueWorkAt, queueWorkKernel, hd, hp]) run
      exact congrArg Prod.fst h

theorem handshakeSendWorker_flushQueues (pid : PeerId) (queues : WorkQueues) :
    ⦃fun g => ⌜flushQueueAt g = some queues⌝⦄ handshakeSendWorker pid
      ⦃⇓? _ g => ⌜flushQueueAt g = some queues⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  unfold handshakeSendWorker
  exact ensures_bind _ _ ((ensures_iff _ _ _).mpr (sendHandshakeInitiation_flushQueues pid queues))
    (fun _ => (ensures_iff _ _ _).mpr (peerPut_spec_queue_variant (some pid) queues))

end Leanux.Proofs.WG.Progress
