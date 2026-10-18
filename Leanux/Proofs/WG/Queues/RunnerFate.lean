import Leanux.Proofs.WG.Queues.RunnerInitialSelection
import Leanux.Proofs.WG.Queues.AdmissionAccounting

/-! The original initialized run supplies the source ledger and every poll
input invariant. The operation and inner position select an admission in
that same certificate. Completeness of the occurrence selection is separate. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.RunnerFate
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged

theorem selected (trace : Trace) (placeholders : Bool)
    (source : (RunnerAccount.rule trace placeholders).relation [] [] (result,w) h next)
    (polls : PollReleaseCaller.Certificates [] h)
    (chosen : (RunnerSelection.account trace placeholders).query operation inner source c) :
    AdmissionRelease.Fate c next [] h :=
  AdmissionRelease.classify
    ((RunnerSelection.account trace placeholders).fates operation inner source chosen) polls

/-- No final funding, poll allocation or completion premise is supplied.
The exact run derives those facts and retains every source-selected admission,
including one removed before its operation or the whole runner returned. -/
theorem normal (trace : Trace) (placeholders : Bool)
    (run : runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h)) :
    ∃next,∃source : (RunnerAccount.rule trace placeholders).relation [] [] (result,w) h next,
      HolderEntry.Inv next [] h w ∧
      ∀operation inner c,(RunnerSelection.account trace placeholders).query operation inner source c→
        AdmissionRelease.Fate c next [] h := by
  obtain ⟨next,source,entry⟩ := RunnerAccount.normal trace placeholders run
  have polls := (PollReleaseRunner.normal trace placeholders run).2
  exact ⟨next,source,entry,fun operation inner c chosen=>selected trace placeholders source polls chosen⟩

/-- Acceptance by the executable runner supplies the same history and final
World, in both placeholder modes and without a trace-shape premise. -/
theorem accepted (trace : Trace) (placeholders : Bool)
    (run : Runner.executeTrace trace placeholders=.ok result) :
    ∃w h next,∃source : (RunnerAccount.rule trace placeholders).relation [] [] (result,w) h next,
      runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h) ∧
      HolderEntry.Inv next [] h w ∧
      ∀operation inner c,(RunnerSelection.account trace placeholders).query operation inner source c→
        AdmissionRelease.Fate c next [] h := by
  obtain ⟨w,h,_,actual,_,_⟩ := RunnerAccount.accepted trace placeholders run
  obtain ⟨next,source,entry,fates⟩ := normal trace placeholders actual
  exact ⟨w,h,next,source,actual,entry,fates⟩

/-- The selected packet occurs once in the final ledger or has a completed
named poll fate and actual release, with no residual copy. -/
theorem partition (trace : Trace) (placeholders : Bool)
    (run : runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h))
    (source : (RunnerAccount.rule trace placeholders).relation [] [] (result,w) h next)
    (chosen : (RunnerSelection.account trace placeholders).query operation inner source c) :
    ∃msg src cs admitted u v before after suffix,
      AdmissionCaller.Step cs admitted msg src u v before after ∧
      ReceiveEffects.Accepted cs admitted msg src u.wg v.wg u.ambient v.ambient c ∧
      h=after++suffix ∧
      ((c∈next ∧ (next.map Carrier.packet).count c.packet=1 ∧
          ¬AdmissionRelease.Removed c after h) ∨
        (c.packet∉next.map Carrier.packet ∧ AdmissionRelease.Removed c after h ∧
          RxHistory.Released h (CarrierIdentity.stamp c.packet))) := by
  obtain ⟨final,certificate,entry⟩ := RunnerAccount.normal trace placeholders run
  have same := RunnerAccount.unique trace placeholders certificate source
  subst final
  have fate := selected trace placeholders source (PollReleaseRunner.normal trace placeholders run).2 chosen
  obtain ⟨msg,src,cs,admitted,u,v,before,after,_,suffix,_,step,admittedHere,finish,outcome⟩ :=
    AdmissionAccounting.partition fate entry
  exact ⟨msg,src,cs,admitted,u,v,before,after,suffix,step,admittedHere,finish,outcome⟩

end Leanux.Proofs.WG.Queues.RxCredits.RunnerFate
