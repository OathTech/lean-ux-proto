import Leanux.Proofs.WG.Origins.RunnerInvariant
import Leanux.Proofs.WG.TransmitSecurity.EmissionOuterFrames

/-! The original Runner transports invariants of the actual sent buffer.
This is proof composition over its existing source, not a second execution.
The prior seven-field store premise omits sent and is not used here. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.EmissionRunner
open Lean Leanux Leanux.Runner Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Origins.HistorySupport Std.Do RunnerInvariant TransmitSecurity

-- The reused array tactic re-elaborates its postcondition; retain resolvable
-- names for the existing Runner helper in that generated syntax.
set_option pp.privateNames true

variable {E : Type}

/-- The literal runner tail preserves safe history for every syscall observer
with the supplied normal-state and failed-prefix contract. -/
theorem runnerTail_wp (I : List E → World → Prop) (S : List E → Prop)
    (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, v.wg.sent = w.wg.sent → I h w → I h v)
    (call : Syscall → PrefixM E Int)
    (calls : ∀ c, PrefixPreserves I S (call c)) (trace : Trace) (w : World) :
    ⦃fun h => ⌜I h w⌝⦄ RxHistory.runnerTail call trace w
    ⦃post⟨fun _ h => ⌜S h⌝, fun _ h => ⌜S h⌝⟩⦄ := by
  have syscall_spec (index : Nat) (w : World) (c : Syscall) :=
    runAtPrefix_wp (show PrefixEnsures I S (call c) (fun _ => I) from calls c) index w
  have ambient : PrefixPreserves I S (liftPrefix (skipAmbient : Leanux.M Unit)) := by
    apply viewLiftPrefix_preserves EmissionOuter.Sent safe store
    exact EmissionOuter.ambient _
  have ambient_spec (index : Nat) (w : World) := runAtPrefix_wp ambient index w
  unfold RxHistory.runnerTail
  repeat' first
    | (runner_invariant_callback call; apply Triple.entails_wp_of_pre_post (syscall_spec _ _ _))
    | (support_runner_wp_call liftPrefix; apply Triple.entails_wp_of_pre_post (ambient_spec _ _))
    | (support_runner_wp_head Pure.pure; apply Triple.pure
        (m := PrefixOuter E) (ps := .except (Nat × Stop) (.arg (List E) .pure)))
    | (support_runner_wp_head throw; apply Triple.entails_wp_of_pre
        (Spec.throw_ExceptT (m := StateM (List E)) (ps := .arg (List E) .pure)))
    | support_runner_wp_throw_bind
    | runner_invariant_bind I
    | runner_invariant_array I
    | support_runner_wp_reduce
    | (support_runner_wp_head ite
       apply (pinned_const _private.Leanux.Proofs.WG.Origins.SupportRunner.«0».Leanux.Proofs.WG.Origins.HistorySupport.supportRunnerTriple_ite))
    | (support_runner_wp_head dite
       apply (pinned_const _private.Leanux.Proofs.WG.Origins.SupportRunner.«0».Leanux.Proofs.WG.Origins.HistorySupport.supportRunnerTriple_dite))
    | maintenance_intro
    | support_runner_wp_match
  all_goals try exact .rfl
  all_goals try exact ⟨fun _ => .rfl, .rfl⟩
  all_goals try (solve | intros; assumption)
  all_goals try (solve | intro history hi; apply store history _ _ ?_ hi; rfl)
  all_goals try (solve | intro history hi; exact safe history _ hi)

/-- The actual fixture establishes the invariant from its exact initial sent
buffer. Every normal or indexed-Stop outcome retains safe history. -/
theorem executeTraceWith_wp (I : List E → World → Prop) (S : List E → Prop)
    (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, v.wg.sent = w.wg.sent → I h w → I h v)
    (call : Syscall → PrefixM E Int)
    (calls : ∀ c, PrefixPreserves I S (call c)) (trace : Trace) (placeholders : Bool)
    (initial : ∀ w, w.wg.sent = (initialWG trace.net trace.bare).sent → I [] w) :
    ⦃fun h => ⌜h = []⌝⦄ RxHistory.executeTraceWith call trace placeholders
    ⦃post⟨fun _ h => ⌜S h⌝, fun _ h => ⌜S h⌝⟩⦄ := by
  have tail_spec (w : World) := runnerTail_wp I S safe store call calls trace w
  have empty : S [] := safe []
    { ambient := { env := harnessEnv, timing := Env.timing },
      tasks := initialTasks trace.rlimit, fs := initialFS trace.net,
      wg := initialWG trace.net trace.bare } (initial _ rfl)
  have boot_store (foreign : Bool) : SameView EmissionOuter.Sent
      (do Net.Fib.bootTables
          if foreign then Net.Fib.inCreatorNs Net.Fib.bootTables : Leanux.M Unit) := by
    apply SameView.bind
    · exact EmissionOuter.routing _
    · intro _
      split
      · exact EmissionOuter.routing _
      · exact SameView.pure _ _
  have boot_initial (w v : World) (x : Unit)
      (hr : (do Net.Fib.bootTables
                if trace.foreign then Net.Fib.inCreatorNs Net.Fib.bootTables : Leanux.M Unit).run w = .ok (x, v))
      (hi : w.wg.sent = (initialWG trace.net trace.bare).sent) :
      v.wg.sent = (initialWG trace.net trace.bare).sent :=
    ((ProjectedAction.iff_run _ _ _).mp (boot_store trace.foreign) w x v hr).trans hi
  unfold RxHistory.executeTraceWith
  by_cases hp : trace.seccompPrefill > 0
  all_goals simp only [hp, ↓reduceIte]
  all_goals cases Env.seccompPrefill trace.seccompPrefill ({} : SeccompWorld) (initialTasks trace.rlimit trace.foreign trace.stepped trace.seccompChild)
  all_goals repeat' first
    | (support_runner_wp_head RxHistory.runnerTail; apply Triple.entails_wp_of_pre_post (tail_spec _))
    | (support_runner_wp_head Pure.pure; apply Triple.pure
        (m := PrefixOuter E) (ps := .except (Nat × Stop) (.arg (List E) .pure)))
    | (support_runner_wp_head throw; apply Triple.entails_wp_of_pre
        (Spec.throw_ExceptT (m := StateM (List E)) (ps := .arg (List E) .pure)))
    | support_runner_wp_throw_bind
    | runner_invariant_bind I
    | runner_invariant_array I
    | support_runner_wp_reduce
    | (support_runner_wp_head ite
       apply (pinned_const _private.Leanux.Proofs.WG.Origins.SupportRunner.«0».Leanux.Proofs.WG.Origins.HistorySupport.supportRunnerTriple_ite))
    | (support_runner_wp_head dite
       apply (pinned_const _private.Leanux.Proofs.WG.Origins.SupportRunner.«0».Leanux.Proofs.WG.Origins.HistorySupport.supportRunnerTriple_dite))
    | maintenance_intro
    | support_runner_wp_match
  all_goals try exact .rfl
  all_goals try exact ⟨fun _ => .rfl, .rfl⟩
  all_goals try (solve | intros; assumption)
  all_goals try (solve | intro history hi; apply store history _ _ ?_ hi; rfl)
  all_goals try (solve | intro history hi; exact safe history _ hi)
  all_goals
    intro history hi
    change history = [] at hi
    subst history
    first
    | exact empty
    | apply initial
      first
      | rfl
      | rename_i hrun
        have hb := boot_initial _ _ _ hrun (by rfl)
        exact hb

/-- The original runner returns JSON or an indexed Stop without losing its
journal invariant. No successful termination or callback totality is assumed. -/
theorem executeTraceWith (I : List E → World → Prop) (S : List E → Prop)
    (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, v.wg.sent = w.wg.sent → I h w → I h v)
    (call : Syscall → PrefixM E Int)
    (calls : ∀ c, PrefixPreserves I S (call c)) (trace : Trace) (placeholders : Bool)
    (initial : ∀ w, w.wg.sent = (initialWG trace.net trace.bare).sent → I [] w) :
    S (runPrefixOuter (RxHistory.executeTraceWith call trace placeholders) []).2 := by
  have checked := (prefixOuter_wp_iff _ _ _ _).mp
    (executeTraceWith_wp I S safe store call calls trace placeholders initial) [] rfl
  cases hr : runPrefixOuter (RxHistory.executeTraceWith call trace placeholders) [] with
  | mk result hist => cases result <;> simpa only [hr] using checked

end Leanux.Proofs.WG.AuthenticatedEffects.EmissionRunner
