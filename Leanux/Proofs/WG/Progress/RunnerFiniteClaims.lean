import Leanux.Proofs.WG.Progress.RunnerFiniteSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux

/-- Every original dispatch agrees with its concrete finite implementation,
on arbitrary projected entry states and without a success premise. -/
theorem original_dispatch_finite_claim (call : Syscall) :
    Campaign2.Product.AgreesOn (fun _ => True) (Leanux.dispatch call)
      (DispatchFinite.call call) := by
  rw [DispatchFinite.call_source]
  intro state pre
  rfl

/-- Complete syscalls, including return-to-user file cleanup and deferred
workers, agree with finite evaluation for every entry and record stream. -/
theorem original_syscall_finite_claim (call : Syscall) :
    Campaign2.Product.AgreesOn (fun _ => True) (Leanux.syscall call)
      (SyscallFinite.call call) := by
  rw [SyscallFinite.call_source]
  intro state pre
  rfl

/-- Every typed trace in either record mode has exactly the finite evaluator's
complete JSON or indexed Stop. No accepted-run or callback-success premise
is used. This is termination of one trace, not of the input server. -/
theorem original_executeTrace_finite_claim (trace : Runner.Trace) (placeholders : Bool) :
    Runner.executeTrace trace placeholders = RunnerFinite.executeTrace trace placeholders :=
  RunnerFinite.executeTrace_source trace placeholders

end Leanux.Proofs.WG.Progress
