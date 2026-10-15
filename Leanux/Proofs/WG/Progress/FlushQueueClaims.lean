import Leanux.Proofs.WG.Progress.FlushQueueSource

set_option autoImplicit false

namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Campaign2 TimerDiscipline

theorem flushedSendQueues_count (pid : PeerId) (d : Device)
    (member : pid ∈ d.sendWorkQueue) :
    flushQueueCount (flushedSendQueues pid d) + 1 = flushQueueCount (workQueues d) := by
  have length := List.length_erase_of_mem member
  have positive := List.length_pos_of_mem member
  simp only [flushQueueCount, flushedSendQueues, workQueues] at *
  omega

theorem flushedClearQueues_count (pid : PeerId) (d : Device)
    (member : pid ∈ d.clearWorkQueue) :
    flushQueueCount (flushedClearQueues pid d) + 1 = flushQueueCount (workQueues d) := by
  have length := List.length_erase_of_mem member
  have positive := List.length_pos_of_mem member
  simp only [flushQueueCount, flushedClearQueues, workQueues] at *
  omega

theorem source_flushed_send_queue (pid : PeerId) (d : Device) :
    Campaign2.Ensures (runFlushedSendWork pid) (fun entry => entry.wg.device = some d)
      (fun _ final => flushQueues final = some (flushedSendQueues pid d) ∧
        (pid ∈ d.sendWorkQueue →
          flushQueueCount (flushedSendQueues pid d) + 1 = flushQueueCount (workQueues d))) := by
  intro w result final pre run
  exact ⟨runFlushedSendWork_queues pid d w result final pre run,
    flushedSendQueues_count pid d⟩

theorem source_flushed_clear_queue (pid : PeerId) (d : Device) :
    Campaign2.Ensures (runFlushedClearWork pid) (fun entry => entry.wg.device = some d)
      (fun _ final => flushQueues final = some (flushedClearQueues pid d) ∧
        (pid ∈ d.clearWorkQueue →
          flushQueueCount (flushedClearQueues pid d) + 1 = flushQueueCount (workQueues d))) := by
  intro w result final pre run
  exact ⟨runFlushedClearWork_queues pid d w result final pre run,
    flushedClearQueues_count pid d⟩

end Leanux.Proofs.WG.Progress
