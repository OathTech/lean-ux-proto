import Leanux.Proofs.WG.Queues.RunnerCoverage
import Leanux.Proofs.WG.TransmitSecurity.BatchNativeSyscall
import Leanux.Proofs.WG.Queues.TxLiveRunner

/-! The unchanged initialized runner carries the actual queued-batch alignment
invariant when its concrete native syscalls preserve it. This generic bridge
retains the existing owner journal; it does not assume an initialized endpoint. -/
namespace Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Runner
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged Leanux.Proofs.Framing
open RetirementSecurity Queues Queues.RxCredits Native Stack

def Inv (h : List RxHistory.Event) (w : World) : Prop :=
  OwnerChecks.Inv h w ∧ Coherent [] [] w.wg

theorem store (same : wgStoreView v.wg=wgStoreView w.wg) (hi : Inv h w) : Inv h v := by
  refine ⟨OwnerControlCalls.store h w v same hi.1,?_⟩
  exact ready_store same hi.2

theorem initial (trace : Trace) (w : World)
    (same : wgStoreView w.wg=wgStoreView (initialWG trace.net trace.bare)) : Inv [] w := by
  refine ⟨OwnerChecks.initial trace.net trace.bare w same,?_⟩
  exact ready_store same (Lifecycle.initial trace.net trace.bare)

/-- The original observer supplies its appended journal and owner checks;
normal native preservation supplies only the independent queued-batch alignment conjunct. -/
theorem syscall (call : Syscall)
    (keeps : Preserves (fun w : World=>Coherent [] [] w.wg) (Leanux.syscall call)) :
    PrefixPreserves Inv OwnerChecks.Safe (RxHistory.syscall call) := by
  intro w h hi
  obtain ⟨suffix,history,safe,post⟩ := OwnerSyscalls.syscall call w h hi.1
  refine ⟨suffix,history,safe,?_⟩
  cases run : (runPrefix (RxHistory.syscall call) w h).1 with
  | error reason=>trivial
  | ok out=>
    rw [run] at post
    exact ⟨post,(hoare_iff_run _ _ _).mp keeps w out.1 out.2 hi.2
      ((RxHistory.syscall_erases call w h).symm.trans run)⟩

/-- This generic runner composition has explicit per-native-call obligations,
which must be discharged before claiming initialized queued-batch alignment preservation. -/
theorem normal (calls : ∀call,Preserves (fun w : World=>Coherent [] [] w.wg) (Leanux.syscall call))
    (trace : Trace) (placeholders : Bool)
    (run : runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h)) :
    Inv h w := by
  exact RunnerInvariant.Normal.executeTraceWith_normal Inv OwnerChecks.Safe
    (fun _ _ hi=>hi.1.safe) (fun _ _ _ same hi=>store same hi)
    RxHistory.syscall (fun call=>syscall call (calls call)) trace placeholders
    (initial trace) run

theorem operation_ready
    (calls : ∀call,Preserves (fun w : World=>Coherent [] [] w.wg) (Leanux.syscall call))
    (trace : Trace) (op : Operation) (state : RunnerOperation.State)
    (hi : Coherent [] [] state.1.wg)
    (run : runPrefixOuter (RunnerOperation.operation RxHistory.syscall trace op state) h=(.ok result,k)) :
    ∃out,result=.yield out ∧ Coherent [] [] out.1.wg := by
  obtain ⟨ret,w,j,front,tail⟩ := RunnerOperation.operation_cut RxHistory.syscall trace op state run
  have initial : Coherent [] [] (RunnerOperation.prepare trace state).wg := ready_store (w := state.1.wg) (v := (RunnerOperation.prepare trace state).wg) rfl hi
  have native := (RxHistory.syscall_erases _ _ _).symm.trans (congrArg Prod.fst front)
  have next := (hoare_iff_run _ _ _).mp (calls _) _ ret w initial native
  obtain ⟨out,same,world⟩ := Queues.TxDisposition.LiveRunner.afterCall_world op state ret w tail
  exact ⟨out,same,world.symm ▸ next⟩

theorem list_ready
    (calls : ∀call,Preserves (fun w : World=>Coherent [] [] w.wg) (Leanux.syscall call))
    (trace : Trace) (ops : List Operation) (state : RunnerOperation.State)
    (hi : Coherent [] [] state.1.wg)
    (run : runPrefixOuter (forIn ops state (RunnerOperation.operation RxHistory.syscall trace)) h=(.ok out,k)) :
    Coherent [] [] out.1.wg := by
  induction ops generalizing state h with
  | nil=>
    simp only [List.forIn_nil,runPrefixOuter_pure,Prod.mk.injEq,Except.ok.injEq] at run
    obtain ⟨rfl,rfl⟩ := run
    exact hi
  | cons op ops ih=>
    obtain ⟨middle,j,front,tail⟩ := RunnerOperationCuts.cons_normal RxHistory.syscall trace op ops state run
    obtain ⟨same,equation,ready⟩ := operation_ready calls trace op state hi front
    cases equation
    exact ih middle ready tail

/-- An operation entry belongs to the actual prefill, boot and ordered loop
prefix, with the exact results/descriptor-dependent syscall conversion. -/
def OperationEntry (trace : Trace) (placeholders : Bool) (index : Nat) : Prop :=
  ∃u v op before j incoming ret returned received admitted,
    runPrefixOuter (ConservationRunner.prefillWith trace.seccompPrefill
      (ConservationRunner.fixture trace placeholders) (pure : World→PrefixOuter RxHistory.Event World)) []=(.ok u,[]) ∧
    runPrefixOuter (ConservationRunner.bootWith trace.net trace.foreign u
      (pure : World→PrefixOuter RxHistory.Event World)) []=(.ok v,[]) ∧
    trace.ops.toList[index]?=some op ∧ before.2.1.size=index ∧
    runPrefixOuter (forIn (trace.ops.toList.take index) (v,#[],#[],#[],#[],#[])
      (RunnerOperation.operation RxHistory.syscall trace)) []=(.ok before,j) ∧
    Coherent [] [] (RunnerOperation.prepare trace before).wg ∧
    (ConservationSyscall.rule (toSyscall before.2.1 before.2.2.1 before.2.1.size op)).relation
      incoming (RunnerOperation.prepare trace before) j ret returned received admitted

/-- Actual normal prefixes derive every syscall input invariant from original
initialization. Per-call contracts remain explicit until concretely discharged. -/
theorem entries (calls : ∀call,Preserves (fun w : World=>Coherent [] [] w.wg) (Leanux.syscall call))
    (trace : Trace) (placeholders : Bool)
    (run : runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h)) :
    ∀index,index<trace.ops.size→OperationEntry trace placeholders index := by
  obtain ⟨final,source,_⟩ := RunnerAccount.normal trace placeholders run
  intro index bound
  obtain ⟨u,v,op,before,j,incoming,ret,returned,received,admitted,
    prefill,boot,position,indexEq,prior,front,_⟩ :=
    RunnerInitializedCuts.account_cut trace placeholders source bound
  have initStore : wgStoreView v.wg=wgStoreView (initialWG trace.net trace.bare) :=
    (Queues.TxDisposition.LiveRunner.boot_store trace.net trace.foreign u v boot).trans
      (Queues.TxDisposition.LiveRunner.prefill_store trace.seccompPrefill (ConservationRunner.fixture trace placeholders) u prefill)
  have ready := list_ready calls trace (trace.ops.toList.take index)
    (v,#[],#[],#[],#[],#[]) (initial trace v initStore).2 prior
  exact ⟨u,v,op,before,j,incoming,ret,returned,received,admitted,
    prefill,boot,position,indexEq,prior,ready_store (w := before.1.wg) (v := (RunnerOperation.prepare trace before).wg) rfl ready,front⟩

end Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Runner
