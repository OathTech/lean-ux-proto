import Leanux.Proofs.WG.Config.QueuedHandshake
import Leanux.Proofs.WG.Config.QueuedHandshakeFindings

/-! A resident, initially pending peer with an empty send queue refutes the legacy empty-queue postcondition when the actual queue record permits requeueing. This is a local model-state witness, with no reachability claim. -/
set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do
namespace RetryQueueFindings
open Leanux.Proofs.WG.Config.QueuedFindings

def emptyPendingDevice : Device := {pendingDevice with sendWorkQueue := []}
def emptyPendingState : WGWorld := {dev := some emptyPendingDevice}
def queueInput (ambient : Ambient) : Ambient := {ambient with
  armRecords := true
  hidden := some [queueRecord]
  unitPeers := [(1, Worker.sendWorker.index, 0)]}

theorem pending_empty_queue_counterexample (ambient : Ambient) :
    emptyPendingDevice.peers[0]? = some pendingPeer ∧
    emptyPendingDevice.sendWorkQueue = [] ∧
    ∃ final after,
      ((queuedAfterClock 0 pendingPeer 0).run emptyPendingState).run (queueInput ambient) =
        .ok (((), final), after) ∧
      final.dev.map Device.sendWorkQueue = some [0] ∧
      ¬ (∃ out, final.dev = some out ∧
        (out.sendWorkQueue = [] ∨ (out.sendWorkQueue = [0] ∧
          out.peers[0]? = some {pendingPeer with refcount := pendingPeer.refcount + 1, handshakePending := true} ∧
          pendingPeer.isDead = false ∧ pendingPeer.handshakePending = false ∧ 0 < pendingPeer.refcount))) := by
  have observation :
      (((queuedAfterClock 0 pendingPeer 0).run emptyPendingState).run (queueInput ambient)).map
        (fun ((result, state), next) => (result, state.dev.map Device.sendWorkQueue, next.hidden)) =
        .ok ((), some [0], some []) := by rfl
  refine ⟨by simp [emptyPendingDevice, pendingDevice], rfl, ?_⟩
  cases run : ((queuedAfterClock 0 pendingPeer 0).run emptyPendingState).run (queueInput ambient) with
  | error stop => simp [run, Except.map] at observation
  | ok output =>
    obtain ⟨⟨result, final⟩, after⟩ := output
    cases result
    have fields : final.dev.map Device.sendWorkQueue = some [0] ∧ after.hidden = some [] := by
      simpa [run, Except.map] using observation
    refine ⟨final, after, rfl, fields.1, ?_⟩
    rintro ⟨out, device, empty | queued⟩
    · rw [device] at fields
      simp [empty] at fields
    · have impossible := queued.2.2.2.1
      change true = false at impossible
      cases impossible
end RetryQueueFindings

end Leanux.Proofs.WG.TimerDiscipline
