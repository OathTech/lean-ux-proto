import Leanux.Proofs.WG.Queues.RunnerInitializedCuts
import Leanux.Proofs.WG.Queues.RunnerFate
import Leanux.Proofs.WG.Queues.IngressCoverage

/-! Independent coverage of every actual initialized ingress source. The run
supplies all cuts, ledgers and invariants before any carrier is considered. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.RunnerCoverage
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged

/-- Each bounded operation is the one in the original initialized execution.
Its actual syscall and entry prefix expose every ingress source position;
accepted carriers have a pending or completed-poll disposition. -/
def Complete (trace : Trace) (placeholders : Bool) (next : Ledger) (history : List RxHistory.Event) : Prop :=
  ∀index,index<trace.ops.size→
    ∃ u v op before j incoming ret returned received admitted,
      runPrefixOuter (ConservationRunner.prefillWith trace.seccompPrefill
        (ConservationRunner.fixture trace placeholders) (pure : World→PrefixOuter RxHistory.Event World)) []=(.ok u,[]) ∧
      runPrefixOuter (ConservationRunner.bootWith trace.net trace.foreign u
        (pure : World→PrefixOuter RxHistory.Event World)) []=(.ok v,[]) ∧
      trace.ops.toList[index]?=some op ∧ before.2.1.size=index ∧
      runPrefixOuter (forIn (trace.ops.toList.take index) (v,#[],#[],#[],#[],#[])
        (RunnerOperation.operation RxHistory.syscall trace)) []=(.ok before,j) ∧
      (ConservationSyscall.rule (toSyscall before.2.1 before.2.2.1 before.2.1.size op)).relation
        incoming (RunnerOperation.prepare trace before) j ret returned received admitted ∧
      (SyscallEntryCuts.TrafficCall (toSyscall before.2.1 before.2.2.1 before.2.1.size op)→
        ∃entered,runPrefix (SyscallEntryCuts.enter (toSyscall before.2.1 before.2.2.1 before.2.1.size op))
          (RunnerOperation.prepare trace before) j=(.ok ((),entered),j) ∧
          IngressCoverage.Complete (toSyscall before.2.1 before.2.2.1 before.2.1.size op)
            incoming entered j (fun _ c=>AdmissionRelease.Fate c next [] history))

/-- Every normal initialized runner derives complete source coverage and the
funded final account. No query, source certificate or invariant is supplied. -/
theorem normal (trace : Trace) (placeholders : Bool)
    (run : runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h)) :
    ∃next,HolderEntry.Inv next [] h w ∧ Complete trace placeholders next h := by
  obtain ⟨next,source,entry,fates⟩ := RunnerFate.normal trace placeholders run
  refine ⟨next,entry,?_⟩
  intro index bound
  obtain ⟨u,v,op,before,j,incoming,ret,returned,received,admitted,
    prefill,boot,position,indexEq,prior,front,lifted⟩ :=
    RunnerInitializedCuts.account_cut trace placeholders source bound
  refine ⟨u,v,op,before,j,incoming,ret,returned,received,admitted,
    prefill,boot,position,indexEq,prior,front,?_⟩
  intro traffic
  obtain ⟨entered,enter,covered⟩ := IngressCoverage.syscall _ traffic front
  exact ⟨entered,enter,IngressCoverage.mono covered
    (fun inner c chosen=>fates index inner c (lifted inner c chosen))⟩

/-- Executable acceptance yields the actual initialized World and journal,
then covers every ingress occurrence in each original operation. Both
placeholder settings and arbitrary typed traces are retained. -/
theorem accepted (trace : Trace) (placeholders : Bool)
    (run : Runner.executeTrace trace placeholders=.ok result) :
    ∃w h next,runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h) ∧
      HolderEntry.Inv next [] h w ∧ Complete trace placeholders next h := by
  obtain ⟨w,h,_,actual,_,_⟩ := RunnerAccount.accepted trace placeholders run
  obtain ⟨next,entry,coverage⟩ := normal trace placeholders actual
  exact ⟨w,h,next,actual,entry,coverage⟩

end Leanux.Proofs.WG.Queues.RxCredits.RunnerCoverage
