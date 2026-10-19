import Leanux.Proofs.WG.RetirementSecurity.TxWorkRemoval
import Leanux.Proofs.WG.Queues.RunnerCoverage

/-! Successful original operation boundaries rule out suspended workers.
This follows from the runner's actual guard, independently of any TX service
invariant. A partial operation or stopped prefix need not satisfy this fact. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork.RunnerBoundary
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Queues.RxCredits

theorem after_call {E : Type} (op : Operation) (state : RunnerOperation.State)
    (ret : Int) (w : World) {h k : List E} {result : ForInStep RunnerOperation.State}
    (run : runPrefixOuter (RunnerOperation.afterCall op state ret w) h=(.ok result,k)) :
    ∃out,result=.yield out ∧ out.1.ambient.suspended=[] ∧ w.ambient.suspended=[] := by
  unfold RunnerOperation.afterCall at run
  obtain ⟨returned,j,start,rest⟩:=RunnerOperation.bind_normal run
  rcases returned with ⟨ignored,world⟩
  cases ignored
  have unchanged : world.ambient.suspended=w.ambient.suspended := by
    have expected := runAtPrefix_erases state.2.1.size w
      (erasesPrefix_lift (skipAmbient : Leanux.M Unit)) h
    rw [start] at expected
    cases native : (skipAmbient : Leanux.M Unit).run w with
    | error reason=>simp only [native,Except.mapError] at expected; cases expected
    | ok value=>
      simp only [native,Except.mapError,Except.ok.injEq] at expected
      cases expected
      exact congrArg Prod.snd ((ProjectedAction.iff_run _ _ _).mp
        (TxActorFrames.lift_ambient TxActorFrames.skip) w () world native)
  cases hidden : world.ambient.hidden with
  | none=>
    cases suspended : world.ambient.suspended with
    | nil=>
      cases raised : world.wg.netRxRaised <;>
        simp only [hidden,suspended,raised,Bool.false_eq_true,↓reduceIte] at rest
      · obtain ⟨branches,l,branchRun,rest⟩:=RunnerOperation.bind_normal rest
        obtain ⟨fired,m,firedRun,rest⟩:=RunnerOperation.bind_normal rest
        cases rest
        exact ⟨_,rfl,suspended,unchanged.symm.trans suspended⟩
      · cases rest
    | cons head tail=>simp only [hidden,suspended,runPrefixOuter_bind] at rest; cases rest
  | some records=>
    cases records with
    | nil=>
      cases suspended : world.ambient.suspended with
      | nil=>
        cases pending : world.ambient.pendingWork with
        | nil=>
          cases raised : world.wg.netRxRaised <;>
            simp only [hidden,suspended,pending,raised,Bool.false_eq_true,↓reduceIte] at rest
          · obtain ⟨branches,l,branchRun,rest⟩:=RunnerOperation.bind_normal rest
            obtain ⟨fired,m,firedRun,rest⟩:=RunnerOperation.bind_normal rest
            cases rest
            exact ⟨_,rfl,suspended,unchanged.symm.trans suspended⟩
          · cases rest
        | cons worker workers=>
          simp only [hidden,suspended,pending] at rest
          cases rest
      | cons head tail=>simp only [hidden,suspended,runPrefixOuter_bind] at rest; cases rest
    | cons head tail=>simp only [hidden,runPrefixOuter_bind] at rest; cases rest

theorem operation {E : Type} (call : Syscall→PrefixM E Int) (trace : Trace)
    (op : Operation) (state : RunnerOperation.State) {h k : List E}
    {result : ForInStep RunnerOperation.State}
    (run : runPrefixOuter (RunnerOperation.operation call trace op state) h=(.ok result,k)) :
    ∃out,result=.yield out ∧ out.1.ambient.suspended=[] := by
  obtain ⟨ret,w,j,_,tail⟩:=RunnerOperation.operation_cut call trace op state run
  obtain ⟨out,same,idle,_⟩:=after_call op state ret w tail
  exact ⟨out,same,idle⟩

theorem list {E : Type} (call : Syscall→PrefixM E Int) (trace : Trace)
    (ops : List Operation) (state : RunnerOperation.State) {h k : List E}
    (initial : state.1.ambient.suspended=[])
    (run : runPrefixOuter (forIn ops state (RunnerOperation.operation call trace)) h=(.ok out,k)) :
    out.1.ambient.suspended=[] := by
  induction ops generalizing state h with
  | nil=>
    simp only [List.forIn_nil,runPrefixOuter_pure,Prod.mk.injEq,Except.ok.injEq] at run
    obtain ⟨rfl,rfl⟩:=run
    exact initial
  | cons op ops ih=>
    rw [List.forIn_cons] at run
    obtain ⟨step,j,front,tail⟩:=RunnerOperation.bind_normal run
    obtain ⟨middle,same,idle⟩:=operation call trace op state front
    cases same
    exact ih middle idle tail

theorem nonempty_prefix {E : Type} (call : Syscall→PrefixM E Int) (trace : Trace)
    (op : Operation) (ops : List Operation) (state : RunnerOperation.State) {h k : List E}
    (run : runPrefixOuter (forIn (op::ops) state (RunnerOperation.operation call trace)) h=(.ok out,k)) :
    out.1.ambient.suspended=[] := by
  rw [List.forIn_cons] at run
  obtain ⟨step,j,front,tail⟩:=RunnerOperation.bind_normal run
  obtain ⟨middle,same,idle⟩:=operation call trace op state front
  cases same
  exact list call trace ops middle idle tail

theorem at_idle (before : At (Covered locals crypt) crypt [] w)
    (idle : w.ambient.suspended=[]) : Serving locals crypt [] w.wg := by
  simpa only [At,Serving,idle,actors,List.filterMap_nil,List.nil_append] using before

end Leanux.Proofs.WG.RetirementSecurity.TxWork.RunnerBoundary
