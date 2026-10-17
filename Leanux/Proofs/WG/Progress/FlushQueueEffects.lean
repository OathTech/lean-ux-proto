import Leanux.Proofs.WG.Progress.FlushQueueModel

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

end Leanux.Proofs.WG.Progress
