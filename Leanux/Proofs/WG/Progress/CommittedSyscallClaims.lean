import Leanux.Proofs.WG.Progress.CommittedSyscallSource
import Leanux.Proofs.WG.Progress.CommittedTrafficClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.CommittedRuns.Syscalls
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues Configuration

theorem original_syscall_journal (call : Syscall) :
    (do let out ← Traffic.observed (syscall call); pure out.1) =
      Campaign2.Product.inspect (Leanux.syscall call) ∧
    Campaign2.Product.Returns (Traffic.observed (syscall call)) (fun _=>True)
      (fun out _=>ValidHistory out.2) :=
  Traffic.observed_correct _ _ (syscall_erases call) (syscall_preserves call)

end Leanux.Proofs.WG.Progress.CommittedRuns.Syscalls
