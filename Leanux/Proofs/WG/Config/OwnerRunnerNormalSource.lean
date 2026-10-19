import Leanux.Proofs.WG.Origins.NormalRunnerInvariant
import Leanux.Proofs.WG.Queues.JointRunnerSource

/-! Local membership-aware variants of C1's three NormalRunnerInvariant rules.
Only syscalls arising from actual trace operations need an address-shape contract;
the original paired runner, normal final state and stopped history remain exact. -/
namespace Leanux.Proofs.WG.Config.OwnerRunnerNormal
open Lean Leanux Leanux.Runner Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Origins.HistorySupport RunnerInvariant RunnerInvariant.Shaped Std.Do
set_option autoImplicit false

variable {E : Type}

/-- The existing source factor retains its actual final World on normal return.
Indexed Stops retain only the supplied safe journal predicate. -/
theorem runnerTail_wp_shaped_variant (I : List E → World → Prop) (S : List E → Prop)
    (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, wgStoreView v.wg = wgStoreView w.wg → I h w → I h v)
    (accept : Syscall → Prop) (call : Syscall → PrefixM E Int)
    (calls : ∀ c, accept c → PrefixPreserves I S (call c)) (trace : Trace)
    (traceCalls : ∀ op, op ∈ trace.ops → ∀ results ends index, accept (toSyscall results ends index op)) (w : World) :
    ⦃fun h => ⌜I h w⌝⦄ RoutingJoint.runnerTailWith call (fun j v=>(j,v)) trace w
    ⦃post⟨fun out h => ⌜I h out.2⌝, fun _ h => ⌜S h⌝⟩⦄ := by
  have syscall_spec (index : Nat) (w : World) (results : Array Int)
      (ends : Array (Option (Nat × Nat))) (op : Operation) (member : op ∈ trace.ops) :=
    runAtPrefix_wp (show PrefixEnsures I S (call (toSyscall results ends index op)) (fun _ => I)
      from calls _ (traceCalls op member results ends index)) index w
  have ambient : PrefixPreserves I S (liftPrefix (skipAmbient : Leanux.M Unit)) := by
    apply viewLiftPrefix_preserves (fun w : World => wgStoreView w.wg) safe store
    intro initial
    exact productAmbient_spec _ (fun w => wgStoreView w.wg = initial) (fun _ _ hi => hi)
  have ambient_spec (index : Nat) (w : World) := runAtPrefix_wp ambient index w
  unfold RoutingJoint.runnerTailWith
  repeat' first
    | (runner_invariant_callback call; apply Triple.entails_wp_of_pre_post (syscall_spec _ _ _ _ _ ?_))
    | (support_runner_wp_call liftPrefix; apply Triple.entails_wp_of_pre_post (ambient_spec _ _))
    | (support_runner_wp_head Pure.pure; apply Triple.pure
        (m := PrefixOuter E) (ps := .except (Nat × Stop) (.arg (List E) .pure)))
    | (support_runner_wp_head throw; apply Triple.entails_wp_of_pre
        (Spec.throw_ExceptT (m := StateM (List E)) (ps := .arg (List E) .pure)))
    | support_runner_wp_throw_bind
    | runner_invariant_bind I
    | shaped_runner_array I
    | support_runner_wp_reduce
    | (support_runner_wp_head ite
       apply (pinned_const _private.Leanux.Proofs.WG.Origins.SupportRunner.«0».Leanux.Proofs.WG.Origins.HistorySupport.supportRunnerTriple_ite))
    | (support_runner_wp_head dite
       apply (pinned_const _private.Leanux.Proofs.WG.Origins.SupportRunner.«0».Leanux.Proofs.WG.Origins.HistorySupport.supportRunnerTriple_dite))
    | maintenance_intro
    | support_runner_wp_match
  all_goals try dsimp only [(pinned_const _private.Leanux.Proofs.WG.Origins.RunnerInvariant.«0».Leanux.Proofs.WG.RunnerInvariant.worldAssertion)] at *
  all_goals try exact .rfl
  all_goals try exact ⟨fun _ => .rfl, .rfl⟩
  all_goals try (solve | intros; assumption)
  all_goals try (solve | intro history hi; apply store history _ _ ?_ hi; rfl)
  all_goals try (solve | intro history hi; exact safe history _ hi)

  all_goals try exact (pinned_const _private.Leanux.Proofs.WG.Origins.ShapedRunnerInvariant.«0».Leanux.Proofs.WG.RunnerInvariant.Shaped.member_cursor) trace _ _ _ (by assumption)

/-- The literal fixture establishes the invariant from the seven WG fields;
the same actual World is retained by the existing paired source factor. -/
theorem executeTraceWith_wp_shaped_variant (I : List E → World → Prop) (S : List E → Prop)
    (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, wgStoreView v.wg = wgStoreView w.wg → I h w → I h v)
    (accept : Syscall → Prop) (call : Syscall → PrefixM E Int)
    (calls : ∀ c, accept c → PrefixPreserves I S (call c)) (trace : Trace)
    (traceCalls : ∀ op, op ∈ trace.ops → ∀ results ends index, accept (toSyscall results ends index op)) (placeholders : Bool)
    (initial : ∀ w, wgStoreView w.wg = wgStoreView (initialWG trace.net trace.bare) → I [] w) :
    ⦃fun h => ⌜h = []⌝⦄ RoutingJoint.executeTraceWith call (fun j v=>(j,v)) trace placeholders
    ⦃post⟨fun out h => ⌜I h out.2⌝, fun _ h => ⌜S h⌝⟩⦄ := by
  have tail_spec (w : World) := runnerTail_wp_shaped_variant I S safe store accept call calls trace traceCalls w
  have empty : S [] := safe []
    { ambient := { env := harnessEnv, timing := Env.timing },
      tasks := initialTasks trace.rlimit, fs := initialFS trace.net,
      wg := initialWG trace.net trace.bare } (initial _ rfl)
  have boot_store (foreign : Bool) : SameView (fun w => wgStoreView w.wg)
      (do Net.Fib.bootTables
          if foreign then Net.Fib.inCreatorNs Net.Fib.bootTables : Leanux.M Unit) := by
    apply SameView.bind
    · intro initial
      exact productRouting_spec _ (fun s => s.2.2.2 = initial)
    · intro _
      split
      · intro initial
        exact productRouting_spec _ (fun s => s.2.2.2 = initial)
      · exact SameView.pure _ _
  have boot_initial (w v : World) (x : Unit)
      (hr : (do Net.Fib.bootTables
                if trace.foreign then Net.Fib.inCreatorNs Net.Fib.bootTables : Leanux.M Unit).run w = .ok (x, v))
      (hi : wgStoreView w.wg = wgStoreView (initialWG trace.net trace.bare)) :
      wgStoreView v.wg = wgStoreView (initialWG trace.net trace.bare) :=
    ((ProjectedAction.iff_run _ _ _).mp (boot_store trace.foreign) w x v hr).trans hi
  unfold RoutingJoint.executeTraceWith
  by_cases hp : trace.seccompPrefill > 0
  all_goals simp only [hp, ↓reduceIte]
  all_goals cases Env.seccompPrefill trace.seccompPrefill ({} : SeccompWorld) (initialTasks trace.rlimit trace.foreign trace.stepped trace.seccompChild)
  all_goals repeat' first
    | (support_runner_wp_head RoutingJoint.runnerTailWith; apply Triple.entails_wp_of_pre_post (tail_spec _))
    | (support_runner_wp_head Pure.pure; apply Triple.pure
        (m := PrefixOuter E) (ps := .except (Nat × Stop) (.arg (List E) .pure)))
    | (support_runner_wp_head throw; apply Triple.entails_wp_of_pre
        (Spec.throw_ExceptT (m := StateM (List E)) (ps := .arg (List E) .pure)))
    | support_runner_wp_throw_bind
    | runner_invariant_bind I
    | shaped_runner_array I
    | support_runner_wp_reduce
    | (support_runner_wp_head ite
       apply (pinned_const _private.Leanux.Proofs.WG.Origins.SupportRunner.«0».Leanux.Proofs.WG.Origins.HistorySupport.supportRunnerTriple_ite))
    | (support_runner_wp_head dite
       apply (pinned_const _private.Leanux.Proofs.WG.Origins.SupportRunner.«0».Leanux.Proofs.WG.Origins.HistorySupport.supportRunnerTriple_dite))
    | maintenance_intro
    | support_runner_wp_match
  all_goals try dsimp only [(pinned_const _private.Leanux.Proofs.WG.Origins.RunnerInvariant.«0».Leanux.Proofs.WG.RunnerInvariant.worldAssertion)] at *
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

/-- An actual normal source run supplies its final invariant without an
assumption about the returned World. -/
theorem executeTraceWith_normal_shaped_variant (I : List E → World → Prop) (S : List E → Prop)
    (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, wgStoreView v.wg = wgStoreView w.wg → I h w → I h v)
    (accept : Syscall → Prop) (call : Syscall → PrefixM E Int)
    (calls : ∀ c, accept c → PrefixPreserves I S (call c)) (trace : Trace)
    (traceCalls : ∀ op, op ∈ trace.ops → ∀ results ends index, accept (toSyscall results ends index op)) (placeholders : Bool)
    (initial : ∀ w, wgStoreView w.wg = wgStoreView (initialWG trace.net trace.bare) → I [] w)
    {result : Json} {w : World} {h : List E}
    (run : runPrefixOuter (RoutingJoint.executeTraceWith call (fun j v=>(j,v)) trace placeholders) []=
      (.ok (result,w),h)) : I h w := by
  have checked := (prefixOuter_wp_iff _ _ _ _).mp
    (executeTraceWith_wp_shaped_variant I S safe store accept call calls trace traceCalls placeholders initial) [] rfl
  simpa only [run] using checked

end Leanux.Proofs.WG.Config.OwnerRunnerNormal
