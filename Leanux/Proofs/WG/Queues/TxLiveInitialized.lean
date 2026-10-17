import Leanux.Proofs.WG.Queues.TxLiveRunner
import Leanux.Proofs.WG.Queues.TxLiveSyscall

/-! The original initialized runner derives live logical encryption-ring bounds
and physical refinement. This does not assert packet residency, exclusion of a
saved refused item, or its later disposal. -/
namespace Leanux.Proofs.WG.Queues.TxDisposition.LiveInitialized
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open LiveFrontier RxCredits

theorem normal (trace : Trace) (placeholders : Bool)
    (run : runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h)) :
    LiveRunner.Inv h w :=
  LiveRunner.normal LiveSyscall.syscall_native trace placeholders run

theorem entries (trace : Trace) (placeholders : Bool)
    (run : runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h)) :
    ∀index,index<trace.ops.size→LiveRunner.OperationEntry trace placeholders index :=
  LiveRunner.entries LiveSyscall.syscall_native trace placeholders run

/-- Executable acceptance supplies the same returned World and every original
operation entry, without an invariant or callback contract as input. -/
theorem accepted (trace : Trace) (placeholders : Bool)
    (run : Runner.executeTrace trace placeholders=.ok result) :
    ∃w h,runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h) ∧
      LiveRunner.Inv h w ∧
      ∀index,index<trace.ops.size→LiveRunner.OperationEntry trace placeholders index := by
  obtain ⟨w,h,_,source,_,_⟩ := RunnerAccount.accepted trace placeholders run
  exact ⟨w,h,source,normal trace placeholders source,entries trace placeholders source⟩

end Leanux.Proofs.WG.Queues.TxDisposition.LiveInitialized
