import Leanux.Proofs.WG.Progress.FlushQueueFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Proofs.WG.Noise TimerDiscipline Std.Do

/-- The original flush, including pending validation, both section reads and the
worker's possibly final peer release, has this exact queue effect on normal return. -/
theorem runFlushedSendWork_queues (pid : PeerId) (d : Device) :
    Ensures (runFlushedSendWork pid) (fun w => w.k.wg = some d)
      (fun _ w => flushQueueAt w = some (flushedSendQueues pid d)) := by
  rw [ensures_iff]
  have hw := handshakeSendWorker_flushQueues pid (flushedSendQueues pid d)
  have hh := hidden_kernel_spec
    (fun k => flushQueueKernel k = some (flushedSendQueues pid d))
  mvcgen [runFlushedSendWork, modifyDev, modifyK, getPeer, getDev, getK,
    setPeer, invariant, hw, hh]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [flushQueueAt, flushQueueKernel, workQueues,
    flushedSendQueues, Option.map_map, Function.comp_def]
  all_goals grind

/-- The original clear flush keeps the send queue and erases the first matching occurrence, if present, of
its selected clear peer, including normal completion that deletes that peer. -/
theorem runFlushedClearWork_queues (pid : PeerId) (d : Device) :
    Ensures (runFlushedClearWork pid) (fun w => w.k.wg = some d)
      (fun _ w => flushQueueAt w = some (flushedClearQueues pid d)) := by
  rw [ensures_iff]
  have hw := queuedExpiredZeroKeyMaterial_flushQueues pid (flushedClearQueues pid d)
  have hh := hidden_kernel_spec
    (fun k => flushQueueKernel k = some (flushedClearQueues pid d))
  mvcgen [runFlushedClearWork, modifyDev, modifyK, hw, hh]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [flushQueueAt, flushQueueKernel, workQueues, flushedClearQueues]

end Leanux.Proofs.WG.Progress
