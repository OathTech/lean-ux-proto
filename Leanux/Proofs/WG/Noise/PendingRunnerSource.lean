import Leanux.Proofs.WG.Noise.PendingSyscallSource
import Leanux.Proofs.WG.Origins.RunnerInvariant

/-! The actual initial fixture and complete original syscall observer establish
pending confirmation-history safety for every typed trace and both input modes.
An outer Stop retains its reached journal, without a returned-state assertion. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingRunner
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues PendingSession

theorem executeTrace (trace : Runner.Trace) (placeholders : Bool) :
    HistorySafe (runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []).2 :=
  RunnerInvariant.executeTraceWith StateInv HistorySafe
    PendingScheduler.safe state_store RxHistory.syscall PendingSyscalls.syscall
    trace placeholders (fun w same => native_initial trace.net trace.bare w.wg same)

end Leanux.Proofs.WG.Noise.PendingRunner
