import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRunnerOperations

/-! A normal runner finish returns the actual loop state. Its administrative
guards may stop the execution, but neither changes the retained journal. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteRunner
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Queues.RxCredits RetirementSecurity
variable {E : Type}

theorem finish_world (trace : Trace) (state : RunnerOperation.State)
    (run : runPrefixOuter (RunnerOperation.finishWith (E:=E) (fun j w=>(j,w)) trace state) h=
      (.ok (result,v),history)) : v=state.1 := by
  unfold RunnerOperation.finishWith at run
  dsimp only at run
  split at run
  · cases run
  · split at run
    · cases run
    · cases run; rfl

/-- The actual normal output keeps the full invariant on its returned World.
The failed branch retains only its explicitly supplied history predicate. -/
theorem tail_endpoint (I J : List E→World→Prop) (S : List E→Prop)
    (safe : ∀ h w, I h w→S h)
    (prepare : ∀ trace state h, I h state.1→I h (RunnerOperation.prepare trace state))
    (close : ∀ h w v, v.wg=w.wg→v.ambient.suspended=[]→w.ambient.suspended=[]→J h w→I h v)
    (call : Syscall→PrefixM E Int)
    (calls : ∀ c, PrefixEnsures I S (call c) (fun _=>J)) (trace : Trace) (w : World) :
    ⦃fun h=>⌜I h w⌝⦄ RoutingJoint.runnerTailWith call (fun j v=>(j,v)) trace w
    ⦃post⟨fun out h=>⌜I h out.2⌝,fun _ h=>⌜S h⌝⟩⦄ := by
  apply (prefixOuter_wp_iff _ _ _ _).mpr
  intro h before
  rw [RunnerOperation.tail_factor,←Array.forIn_toList,runPrefixOuter_bind]
  have checked := (prefixOuter_wp_iff _ _ _ _).mp
    (operations I J S prepare close call calls trace trace.ops.toList (w,#[],#[],#[],#[],#[])) h before
  cases source : runPrefixOuter
      (forIn trace.ops.toList (w,#[],#[],#[],#[],#[]) (RunnerOperation.operation call trace)) h with
  | mk outcome k =>
    rw [source] at checked
    cases outcome with
    | error reason => exact checked
    | ok state =>
      dsimp only
      have quiet := finish_quiet (E:=E) trace state k
      cases ending : runPrefixOuter (RunnerOperation.finishWith (fun j v=>(j,v)) trace state) k with
      | mk outcome j =>
        rw [ending] at quiet
        change j=k at quiet
        cases outcome with
        | error reason => simpa only [quiet] using safe k state.1 checked
        | ok out =>
          have world := finish_world trace state ending
          simpa only [quiet,world] using checked

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteRunner
