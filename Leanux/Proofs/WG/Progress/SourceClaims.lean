import Leanux.Proofs.WG.Progress.SchedulerSourceClaims
import Leanux.Proofs.WG.Progress.BatchBacklog

namespace Leanux.Proofs.WG.Progress.SourceClaims
open Leanux Leanux.Env

/-- The historical two-operation trace is rejected by the actual runner's
batch completion boundary; it no longer supplies an accepted backlog witness. -/
theorem original_pending_batch_accepted : accepted = false :=
  pendingTrace_accepted

/-- The old direct-call fixture omits current FIB boot and returns no backlog.
BatchBacklog proves its exact route/source-disagreement Stop separately. -/
theorem original_pending_batch_state : backlog = none :=
  pendingTrace_backlog

end Leanux.Proofs.WG.Progress.SourceClaims
