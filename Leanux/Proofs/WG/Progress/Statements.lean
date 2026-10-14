import Leanux.Proofs.WG.Progress.BatchBacklog

namespace Leanux.Proofs.WG.Progress

/-- The actual runner accepts this two-operation trace with no receive
dispatch after a batch queues a handshake message. Proved by kernel reduction. -/
theorem original_pending_batch_accepted : accepted = true :=
  pendingTrace_accepted

/-- The same initialized fixture and two original syscalls leave one
handshake queue item and the receive-worker identity pending, although all
records are consumed, no activation is suspended and NET_RX is not raised. -/
theorem original_pending_batch_state :
    backlog = some (1, 1, [1], some 0, 0, false) :=
  pendingTrace_backlog

end Leanux.Proofs.WG.Progress
