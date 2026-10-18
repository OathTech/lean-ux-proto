import Leanux.Proofs.WG.Noise.PendingSchedulerSource
import Leanux.Proofs.WG.Noise.PendingCryptSource
import Leanux.Proofs.WG.Noise.PendingTransmitSource
import Leanux.Proofs.WG.Noise.PendingTimerSource

/-! All actual scheduler and deferred callbacks have concrete pending-history
contracts. No worker or timer preservation obligation remains as a premise. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingScheduler
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues PendingSession

theorem actualWorkers : Workers :=
  ⟨PendingCrypt.encrypt_iteration, PendingCrypt.decrypt_iteration, PendingTransmit.observed⟩

theorem actualLeaves : DeferredLeaves :=
  ⟨PendingTimers.dispatch_pending_variant, PendingTimers.placeholder_pending_variant⟩

theorem actual_dispatch (worker : Worker) :
    PrefixPreserves StateInv HistorySafe (RxHistory.dispatch worker) :=
  dispatch actualWorkers worker

theorem actual_schedule (caller : Option Worker) :
    PrefixPreserves StateInv HistorySafe (RxHistory.schedule caller) :=
  schedule actualWorkers caller

theorem actual_nested (worker : Worker) :
    PrefixPreserves StateInv HistorySafe (RxHistory.nestedResched worker) :=
  nested actualWorkers worker

theorem actual_deferred (call : EnvDeferredCall) :
    PrefixPreserves StateInv HistorySafe (RxHistory.deferred call) :=
  deferred actualWorkers actualLeaves call

end Leanux.Proofs.WG.Noise.PendingScheduler
