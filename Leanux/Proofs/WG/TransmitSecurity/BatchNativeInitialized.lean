import Leanux.Proofs.WG.TransmitSecurity.BatchNativeRunner


/-! The actual initialized runner supplies batch peer/key alignment at
every native syscall entry and returned world. Native callback contracts are
discharged; no incoming alignment or per-call coverage premise remains. -/
namespace Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Initialized
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open RetirementSecurity Queues Queues.RxCredits Native Stack

theorem normal (trace : Trace) (placeholders : Bool)
    (run : runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h)) :
    BatchCoherence.Runner.Inv h w :=
  BatchCoherence.Runner.normal Syscalls.syscall_native trace placeholders run

theorem entries (trace : Trace) (placeholders : Bool)
    (run : runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h)) :
    ∀index,index<trace.ops.size→BatchCoherence.Runner.OperationEntry trace placeholders index :=
  BatchCoherence.Runner.entries Syscalls.syscall_native trace placeholders run

/-- Executable acceptance supplies the same returned World and every original
operation entry, without an invariant or callback contract as input. -/
theorem accepted (trace : Trace) (placeholders : Bool)
    (run : Runner.executeTrace trace placeholders=.ok result) :
    ∃w h,runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h) ∧
      BatchCoherence.Runner.Inv h w ∧
      ∀index,index<trace.ops.size→BatchCoherence.Runner.OperationEntry trace placeholders index := by
  obtain ⟨w,h,_,source,_,_⟩ := RunnerAccount.accepted trace placeholders run
  exact ⟨w,h,source,normal trace placeholders source,entries trace placeholders source⟩

end Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Initialized
