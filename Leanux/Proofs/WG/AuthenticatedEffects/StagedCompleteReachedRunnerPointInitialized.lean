import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRunnerPointFraming

/-! The initialized source skeleton derives its actual entry certificates.
Normal operation guards re-establish idle service before the next original
operation. No incoming ledger or destructor precondition is assumed. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Runner.Points
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CausalJournal RetirementSecurity

theorem after_call_framed (op : Operation) (state : State) (ret : Int) (w : World)
    (before : CompleteProduct.Carrier h w) : Framed (afterCallShape op state ret w) h := by
  unfold afterCallShape
  apply Framed.marked _ _ before
  apply Framed.bind (.native _ before)
  intro out last performed
  rcases out with ⟨ignored,v⟩
  have next := Native.normal (.skip state.2.1.size w) before performed
  apply Framed.marked _ _ next
  rcases v with ⟨ambient,tasks,seccomp,fs,wg,fixture⟩
  rcases ambient with ⟨_,_,_,_,_,hidden,_,_,suspended,_,_,_,_,_,_,_,_,_⟩
  rcases wg with ⟨_,_,_,_,_,_,_,_,_,_,_,_,raised,_,_,_,_,_,_,_⟩
  cases hidden with
  | none =>
    cases suspended <;> cases raised
    all_goals repeat' first
      | runner_frame_uncast
      | exact Framed.pure _
      | exact Framed.stopped _
      | exact array_pure_framed _ _ _
      | apply Framed.bind
      | (intro)
      | (dsimp +failIfUnchanged only)
      | (exact True.intro)
  | some records =>
    cases records <;> cases suspended <;> cases raised
    all_goals repeat' first
      | runner_frame_uncast
      | exact Framed.pure _
      | exact Framed.stopped _
      | exact array_pure_framed _ _ _
      | apply Framed.bind
      | (intro)
      | (dsimp +failIfUnchanged only)
      | (exact True.intro)


theorem operation_framed (trace : Trace) (op : Operation) (state : State)
    (before : CompletePrefix.Runner.Entry h state.1) : Framed (operationShape trace op state) h := by
  unfold operationShape
  apply Framed.marked _ _ before.1.1
  have prepared := CompletePrefix.Runner.prepare trace state h before
  apply Framed.bind (.marked _ _ prepared.1.1 (syscall_framed _ _ _ prepared))
  intro out last performed
  exact after_call_framed op state out.1 out.2
    (checked_normal (CompletePrefix.Runner.syscall _) prepared performed).1.1

theorem operation_normal (trace : Trace) (op : Operation) (state : State)
    (before : CompletePrefix.Runner.Entry h state.1)
    (performed : runPrefixOuter (RunnerOperation.operation (Driver.syscallObserved hooks) trace op state) h=(.ok decision,last)) :
    CompletePrefix.Runner.Entry last decision.value.1 := by
  have checked := (prefixOuter_wp_iff _ _ _ _).mp
    (CompleteRunner.operation CompletePrefix.Runner.Entry CompletePrefix.Runner.Exit
      (CompletePrefix.All CompleteProduct.Safe) CompletePrefix.Runner.prepare CompletePrefix.Runner.close
      (Driver.syscallObserved hooks) CompletePrefix.Runner.syscall trace op state) h before
  rw [performed] at checked
  obtain ⟨out,rfl,next⟩ := checked
  exact next

theorem finish_framed (trace : Trace) (state : State)
    (before : CompleteProduct.Carrier h state.1) : Framed (finishShape trace state) h := by
  unfold finishShape
  apply Framed.marked _ _ before
  split
  · runner_frame_uncast
    repeat' runner_frame_uncast
    exact .stopped _
  · split
    · repeat' runner_frame_uncast
      exact .stopped _
    · repeat' runner_frame_uncast
      exact .pure _

theorem tail_framed (trace : Trace) (w : World)
    (before : CompletePrefix.Runner.Entry h w) : Framed (tailShape trace w) h := by
  unfold tailShape
  repeat' runner_frame_uncast
  apply Framed.bind (list_framed _ _ _ _ (fun s h=>CompletePrefix.Runner.Entry h s.1)
    (fun op state h before=>operation_framed trace op state before)
    (fun op state h decision last before performed=>operation_normal trace op state before performed) before)
  intro state last performed
  have checked := (prefixOuter_wp_iff _ _ _ _).mp
    (CompleteRunner.operations CompletePrefix.Runner.Entry CompletePrefix.Runner.Exit
      (CompletePrefix.All CompleteProduct.Safe) CompletePrefix.Runner.prepare CompletePrefix.Runner.close
      (Driver.syscallObserved hooks) CompletePrefix.Runner.syscall trace trace.ops.toList
        (w,#[],#[],#[],#[],#[])) h before
  rw [performed] at checked
  exact finish_framed trace state checked.1.1

/-- All canonical outer points have native entry certificates from the literal
initialized fixture and original successful loop prefixes. Child interiors
remain exactly the five obligations of ChildContracts. -/
theorem initialized_framed (trace : Trace) (placeholders : Bool) :
    Framed (executeShape trace placeholders) [] := by
  have initial : CompletePrefix.Runner.Entry [] (ConservationRunner.fixture trace placeholders) :=
    CompletePrefix.Runner.initial trace.net trace.bare _ rfl rfl
  unfold executeShape
  apply Framed.marked _ _ initial.1.1
  repeat' runner_frame_uncast
  apply Framed.bind (.native _ initial.1.1)
  intro u h pref
  have quiet := CompleteRunner.prefill_quiet (E:=Event) trace.seccompPrefill
    (ConservationRunner.fixture trace placeholders) []
  rw [pref] at quiet
  change h=[] at quiet
  subst h
  have prestore := CompleteRunner.prefill_store trace.seccompPrefill (ConservationRunner.fixture trace placeholders) u pref
  have preaccount := Native.normal (.prefill trace.seccompPrefill (ConservationRunner.fixture trace placeholders)) initial.1.1 pref
  repeat' runner_frame_uncast
  apply Framed.bind (.native _ preaccount)
  intro v h boot
  have quiet := CompleteRunner.boot_quiet (E:=Event) trace.net trace.foreign u []
  rw [boot] at quiet
  change h=[] at quiet
  subst h
  have store := (CompleteRunner.boot_store trace.net trace.foreign u v boot).trans prestore
  exact tail_framed trace v (CompletePrefix.Runner.initial trace.net trace.bare v store
    (TxWork.RunnerBoundary.initial_idle trace placeholders pref boot))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Runner.Points
