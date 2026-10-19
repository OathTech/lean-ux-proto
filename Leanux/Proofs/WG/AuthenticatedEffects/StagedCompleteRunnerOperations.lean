import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRunnerFrames

/-! The original operation loop may use a stronger idle entry than its
syscall endpoint. Its actual afterCall guard restores that entry. Stopped
syscalls and stopped administrative tails retain the reached safe journal. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteRunner
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Queues.RxCredits RetirementSecurity

variable {E : Type}

theorem operation (I J : List E → World → Prop) (S : List E → Prop)
    (prepare : ∀ trace state h, I h state.1 → I h (RunnerOperation.prepare trace state))
    (close : ∀ h w v, v.wg=w.wg → v.ambient.suspended=[] → w.ambient.suspended=[] →
      J h w → I h v)
    (call : Syscall → PrefixM E Int)
    (calls : ∀ c, PrefixEnsures I S (call c) (fun _ => J))
    (trace : Trace) (op : Operation) (state : RunnerOperation.State) :
    ⦃fun h => ⌜I h state.1⌝⦄ RunnerOperation.operation call trace op state
    ⦃post⟨fun step h => ⌜∃ out, step=.yield out ∧ I h out.1⌝,fun _ h => ⌜S h⌝⟩⦄ := by
  apply (prefixOuter_wp_iff _ _ _ _).mpr
  intro h before
  have entered := prepare trace state h before
  obtain ⟨suffix,history,safe,post⟩ := calls
    (toSyscall state.2.1 state.2.2.1 state.2.1.size op)
    (RunnerOperation.prepare trace state) h entered
  unfold RunnerOperation.operation
  rw [runPrefixOuter_bind,runAtPrefix_run]
  cases source : runPrefix (call (toSyscall state.2.1 state.2.2.1 state.2.1.size op))
      (RunnerOperation.prepare trace state) h with
  | mk outcome k =>
    rw [source] at safe post
    cases outcome with
    | error reason => exact safe
    | ok value =>
      obtain ⟨ret,w⟩ := value
      simp only [Except.mapError]
      have quiet := afterCall_quiet (E:=E) op state ret w k
      cases tail : runPrefixOuter (RunnerOperation.afterCall op state ret w) k with
      | mk outcome j =>
        rw [tail] at quiet
        change j=k at quiet
        cases outcome with
        | error reason => simpa only [quiet] using safe
        | ok step =>
          obtain ⟨out,same,idle,incoming⟩ := TxWork.RunnerBoundary.after_call op state ret w tail
          obtain ⟨other,otherSame,world⟩ := TxDisposition.LiveRunner.afterCall_world op state ret w tail
          have equality : other=out := ForInStep.yield.inj (otherSame.symm.trans same)
          subst other
          exact ⟨out,same,by simpa only [quiet] using close k w out.1 world idle incoming post⟩

theorem operations (I J : List E → World → Prop) (S : List E → Prop)
    (prepare : ∀ trace state h, I h state.1 → I h (RunnerOperation.prepare trace state))
    (close : ∀ h w v, v.wg=w.wg → v.ambient.suspended=[] → w.ambient.suspended=[] →
      J h w → I h v)
    (call : Syscall → PrefixM E Int)
    (calls : ∀ c, PrefixEnsures I S (call c) (fun _ => J))
    (trace : Trace) (ops : List Operation) (state : RunnerOperation.State) :
    ⦃fun h => ⌜I h state.1⌝⦄ forIn ops state (RunnerOperation.operation call trace)
    ⦃post⟨fun out h => ⌜I h out.1⌝,fun _ h => ⌜S h⌝⟩⦄ := by
  apply (prefixOuter_wp_iff _ _ _ _).mpr
  intro h before
  induction ops generalizing state h with
  | nil => simpa only [List.forIn_nil,runPrefixOuter_pure] using before
  | cons op ops ih =>
    rw [List.forIn_cons,runPrefixOuter_bind]
    have first := (prefixOuter_wp_iff _ _ _ _).mp
      (operation I J S prepare close call calls trace op state) h before
    cases source : runPrefixOuter (RunnerOperation.operation call trace op state) h with
    | mk outcome k =>
      rw [source] at first
      cases outcome with
      | error reason => exact first
      | ok step =>
        obtain ⟨out,rfl,next⟩ := first
        exact ih out k next

/-- Normal completion retains the actual final World; either kind of Stop
keeps the safety assertion on the journal reached before that Stop. -/
theorem tail (I J : List E → World → Prop) (S : List E → Prop)
    (safe : ∀ h w, I h w → S h)
    (prepare : ∀ trace state h, I h state.1 → I h (RunnerOperation.prepare trace state))
    (close : ∀ h w v, v.wg=w.wg → v.ambient.suspended=[] → w.ambient.suspended=[] →
      J h w → I h v)
    (call : Syscall → PrefixM E Int)
    (calls : ∀ c, PrefixEnsures I S (call c) (fun _ => J))
    (trace : Trace) (w : World) :
    ⦃fun h => ⌜I h w⌝⦄ RoutingJoint.runnerTailWith call (fun j v => (j,v)) trace w
    ⦃post⟨fun _ h => ⌜S h⌝,fun _ h => ⌜S h⌝⟩⦄ := by
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
      have good := safe k state.1 checked
      cases ending : runPrefixOuter (RunnerOperation.finishWith (fun j v => (j,v)) trace state) k with
      | mk result j =>
        rw [ending] at quiet
        change j=k at quiet
        cases result <;> simpa only [quiet] using good

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteRunner
