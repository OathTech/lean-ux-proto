import Leanux.Proofs.WG.RetirementSecurity.OccurrenceRunner


/-! The original initialized runner derives exclusive actual TX packet owners,
pending encryption alias ownership, and packet residency. This state invariant
does not yet carry historical one-encryption receipts or key-credit ownership. -/
namespace Leanux.Proofs.WG.RetirementSecurity.OccurrenceInitialized
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits OccurrenceStack

theorem normal (trace : Trace) (placeholders : Bool)
    (run : runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h)) :
    OccurrenceRunner.Inv h w :=
  OccurrenceRunner.normal OccurrenceSyscall.syscall_native trace placeholders run

theorem entries (trace : Trace) (placeholders : Bool)
    (run : runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h)) :
    ∀index,index<trace.ops.size→OccurrenceRunner.OperationEntry trace placeholders index :=
  OccurrenceRunner.entries OccurrenceSyscall.syscall_native trace placeholders run

/-- Executable acceptance supplies the same returned World and every original
operation entry, without an invariant or callback contract as input. -/
theorem accepted (trace : Trace) (placeholders : Bool)
    (run : Runner.executeTrace trace placeholders=.ok result) :
    ∃w h,runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h) ∧
      OccurrenceRunner.Inv h w ∧
      ∀index,index<trace.ops.size→OccurrenceRunner.OperationEntry trace placeholders index := by
  obtain ⟨w,h,_,source,_,_⟩ := RunnerAccount.accepted trace placeholders run
  exact ⟨w,h,source,normal trace placeholders source,entries trace placeholders source⟩

end Leanux.Proofs.WG.RetirementSecurity.OccurrenceInitialized
