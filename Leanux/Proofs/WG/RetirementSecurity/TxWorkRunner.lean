import Leanux.Proofs.WG.RetirementSecurity.TxWorkSyscall

/-! Actual initialized runner transport for queue-head TX service. Native
operation guards discharge suspension at each boundary; no service or schedule
invariant is supplied by the caller. No alternative runner is introduced. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork.Runner
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits

def Inv (w : World) : Prop := Serving [] [] [] w.wg ∧ w.ambient.suspended=[]

theorem operation (trace : Trace) (op : Operation) (state : RunnerOperation.State)
    (before : Inv state.1)
    (run : runPrefixOuter (RunnerOperation.operation RxHistory.syscall trace op state) h=(.ok result,k)) :
    ∃out,result=.yield out ∧ Inv out.1 := by
  obtain ⟨ret,w,j,front,tail⟩:=RunnerOperation.operation_cut RxHistory.syscall trace op state run
  have prepared : Inv (RunnerOperation.prepare trace state) :=
    ⟨serving_store_transport (w:=state.1.wg) (v:=(RunnerOperation.prepare trace state).wg) rfl before.1,before.2⟩
  have native := (RxHistory.syscall_erases _ _ _).symm.trans (congrArg Prod.fst front)
  have serviced := syscall_boundary_actor _ (serving_add_suspended prepared.1) prepared.2 native
  obtain ⟨out,same,idle,returnedIdle⟩:=RunnerBoundary.after_call op state ret w tail
  obtain ⟨other,otherSame,world⟩:=Queues.TxDisposition.LiveRunner.afterCall_world op state ret w tail
  have equal : other=out := ForInStep.yield.inj (otherSame.symm.trans same)
  subst other
  exact ⟨out,same,world.symm ▸ serving_without_actors serviced returnedIdle,idle⟩

theorem list (trace : Trace) (ops : List Operation) (state : RunnerOperation.State)
    (before : Inv state.1)
    (run : runPrefixOuter (forIn ops state (RunnerOperation.operation RxHistory.syscall trace)) h=(.ok out,k)) :
    Inv out.1 := by
  induction ops generalizing state h with
  | nil=>
    simp only [List.forIn_nil,runPrefixOuter_pure,Prod.mk.injEq,Except.ok.injEq] at run
    obtain ⟨rfl,rfl⟩:=run
    exact before
  | cons op ops ih=>
    obtain ⟨middle,j,front,tail⟩:=RunnerOperationCuts.cons_normal RxHistory.syscall trace op ops state run
    obtain ⟨same,equation,ready⟩:=operation trace op state before front
    cases equation
    exact ih middle ready tail

theorem initial (trace : Trace) (placeholders : Bool) {u v : World}
    (prefill : runPrefixOuter (ConservationRunner.prefillWith trace.seccompPrefill
      (ConservationRunner.fixture trace placeholders) (pure : World→PrefixOuter RxHistory.Event World)) []=(.ok u,[]))
    (boot : runPrefixOuter (ConservationRunner.bootWith trace.net trace.foreign u
      (pure : World→PrefixOuter RxHistory.Event World)) []=(.ok v,[])) : Inv v := by
  have same : wgStoreView v.wg=wgStoreView (initialWG trace.net trace.bare) :=
    (Queues.TxDisposition.LiveRunner.boot_store trace.net trace.foreign u v boot).trans
      (Queues.TxDisposition.LiveRunner.prefill_store trace.seccompPrefill (ConservationRunner.fixture trace placeholders) u prefill)
  have idle:=RunnerBoundary.initial_idle trace placeholders prefill boot
  exact ⟨serving_without_actors (initial_at trace.net trace.bare v same) idle,idle⟩

/-- The exact actual prefix before every normal initialized syscall supplies
queue service and an empty suspension list, including operation zero. -/
theorem entries (trace : Trace) (placeholders : Bool)
    (run : runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h))
    (index : Nat) (bound : index<trace.ops.size) :
    ∃u v op before j incoming ret returned received admitted,
      runPrefixOuter (ConservationRunner.prefillWith trace.seccompPrefill
        (ConservationRunner.fixture trace placeholders) (pure : World→PrefixOuter RxHistory.Event World)) []=(.ok u,[]) ∧
      runPrefixOuter (ConservationRunner.bootWith trace.net trace.foreign u
        (pure : World→PrefixOuter RxHistory.Event World)) []=(.ok v,[]) ∧
      trace.ops.toList[index]?=some op ∧ before.2.1.size=index ∧
      runPrefixOuter (forIn (trace.ops.toList.take index) (v,#[],#[],#[],#[],#[])
        (RunnerOperation.operation RxHistory.syscall trace)) []=(.ok before,j) ∧
      Inv (RunnerOperation.prepare trace before) ∧
      (ConservationSyscall.rule (toSyscall before.2.1 before.2.2.1 before.2.1.size op)).relation
        incoming (RunnerOperation.prepare trace before) j ret returned received admitted := by
  obtain ⟨final,source,_⟩:=RunnerAccount.normal trace placeholders run
  obtain ⟨u,v,op,before,j,incoming,ret,returned,received,admitted,
    prefill,boot,position,indexEq,prior,front,_⟩:=
    RunnerInitializedCuts.account_cut trace placeholders source bound
  have ready:=list trace (trace.ops.toList.take index) (v,#[],#[],#[],#[],#[])
    (initial trace placeholders prefill boot) prior
  exact ⟨u,v,op,before,j,incoming,ret,returned,received,admitted,prefill,boot,position,indexEq,prior,
    ⟨serving_store_transport (w:=before.1.wg) (v:=(RunnerOperation.prepare trace before).wg) rfl ready.1,ready.2⟩,front⟩

end Leanux.Proofs.WG.RetirementSecurity.TxWork.Runner
