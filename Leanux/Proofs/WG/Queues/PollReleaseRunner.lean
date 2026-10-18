import Leanux.Proofs.WG.Origins.NormalRunnerInvariant
import Leanux.Proofs.WG.Queues.PollReleaseCaller
import Leanux.Proofs.WG.Queues.RunnerAccount

/-! Completed initialized runs capture the allocation-valid input of every
actual poll invocation that contributed a removal. Indexed Stops keep the
existing owner-safe journal but do not claim completion or a final state. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.PollReleaseRunner
open Lean Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

/-- Both placeholder modes use the original WGStore7 fixture and actual
syscalls. The final invariant is derived on the same paired source run. -/
theorem normal (trace : Trace) (placeholders : Bool)
    (run : runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h)) :
    PollReleaseCaller.Inv [] h w := by
  apply RunnerInvariant.Normal.executeTraceWith_normal (PollReleaseCaller.Inv []) OwnerChecks.Safe
    (fun _ _ hi=>hi.1.safe)
    (fun h w v eq hi=>⟨OwnerControlCalls.store h w v eq hi.1,hi.2⟩)
    RxHistory.syscall PollReleaseCaller.syscall trace placeholders _ run
  intro v eq
  exact ⟨OwnerChecks.initial trace.net trace.bare v eq,PollReleaseCaller.initial []⟩

/-- The original JSON observer has the identical actual final World. No
certificate or allocation invariant for that World is assumed. -/
theorem history_normal (trace : Trace) (placeholders : Bool)
    (run : runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []=(.ok result,h)) :
    PollReleaseCaller.Certificates [] h := by
  obtain ⟨w,_,actual,_,_⟩ := RunnerAccount.history_normal trace placeholders run
  exact (normal trace placeholders actual).2

/-- An exact selected occurrence retains its own invocation and earlier cut,
including when equal-valued removal events occur elsewhere in the journal. -/
theorem selected (trace : Trace) (placeholders : Bool)
    (run : runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []=(.ok result,h))
    (position : h=pre++RxHistory.Event.removed n skb stamp::post) :
    PollReleaseCaller.Certificate pre n skb stamp h := by
  simpa only [List.nil_append] using
    (history_normal trace placeholders run).selected (by simpa only [List.nil_append] using position)

/-- Each selected completed-run removal has an actual packet release in its
own completed poll suffix, with allocation validity at that poll's input. -/
theorem selected_release (trace : Trace) (placeholders : Bool)
    (run : runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []=(.ok result,h))
    (position : h=pre++RxHistory.Event.removed n skb stamp::post) :
    ∃ incoming w pid budget out v before after tail,
      pre=incoming++before.map RxHistory.promote ∧
      AllocationInv (RxHistory.prior incoming) w.wg ∧
      runPrefix (RxJoint.poll pid budget) w (RxJoint.seed (RxHistory.prior incoming))=
        (.ok (out,v),RxJoint.seed (RxHistory.prior incoming)++(before++RxJoint.Event.removed n skb stamp::after)) ∧
      h=incoming++(before++RxJoint.Event.removed n skb stamp::after).map RxHistory.promote++tail ∧
      RxHistory.Released ((before++RxJoint.Event.removed n skb stamp::after).map RxHistory.promote) stamp :=
  (selected trace placeholders run position).release

/-- Acceptance by the executable runner supplies this same observed run and
normal invariant; residual carriers are not required to be absent. -/
theorem accepted (trace : Trace) (placeholders : Bool)
    (run : Runner.executeTrace trace placeholders=.ok result) :
    ∃w h,runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h) ∧
      PollReleaseCaller.Inv [] h w := by
  obtain ⟨w,h,_,actual,_,_⟩ := RunnerAccount.accepted trace placeholders run
  exact ⟨w,h,actual,normal trace placeholders actual⟩

end Leanux.Proofs.WG.Queues.RxCredits.PollReleaseRunner
