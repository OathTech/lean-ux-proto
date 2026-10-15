import Leanux.Proofs.WG.TimerDiscipline.SendView

namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Campaign2 TimerDiscipline

/-- The two work queues drained by peer removal, with multiplicity retained. -/
def flushQueues (s : Snapshot) : Option WorkQueues := s.wg.device.map workQueues

def flushQueueCount (queues : WorkQueues) : Nat := queues.1.length + queues.2.length

/-- One original send flush erases only the first matching send occurrence, if present. -/
def flushedSendQueues (pid : PeerId) (d : Device) : WorkQueues :=
  (d.sendWorkQueue.erase pid, d.clearWorkQueue)

/-- One original clear flush erases only the first matching clear occurrence, if present. -/
def flushedClearQueues (pid : PeerId) (d : Device) : WorkQueues :=
  (d.sendWorkQueue, d.clearWorkQueue.erase pid)

end Leanux.Proofs.WG.Progress
