import Leanux.Proofs.WG.Progress.CommittedInitializedClaims
import Leanux.Proofs.WG.Progress.CommittedSyscallCompletionSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.CommittedRuns.Initialized
open Lean Leanux Leanux.Runner Leanux.Proofs.Logged Std.Do

/-- Successful completion of the original paired runner forces all its actual
committed activation receipts to be normal. Failed traces keep their journal
but need not satisfy this normal-only predicate. -/
theorem observed_normal (trace : Trace) (placeholders : Bool) (output : Json)
    (final : World) (history : List Receipt)
    (accepted : runPrefixOuter (observed trace placeholders) [] =
      (.ok (output,final),history)) : NormalHistory history := by
  exact RunnerInvariant.Normal.executeTraceWith_normal
    (fun h _ => NormalHistory h) (fun _ => True)
    (fun _ _ _ => trivial) (fun _ _ _ _ h => h)
    Syscalls.syscall Syscalls.Completion.syscall_preserves trace placeholders
    (fun _ _ receipt member => by cases member) accepted

end Leanux.Proofs.WG.Progress.CommittedRuns.Initialized
