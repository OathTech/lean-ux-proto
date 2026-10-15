import Leanux.Proofs.WG.Lifetimes.RunnerAudit
import Leanux.Proofs.WG.Lifetimes.AllocationInitial

/-! Initialized allocation-identity access safety for every typed Runner trace.
Successful and failed executions retain safe committed observations and valid
saved consistency-filter entries; copied trial histories remain separate. -/
namespace Leanux.Proofs.WG.Lifetimes
open Lean Leanux Leanux.Runner Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
set_option maxHeartbeats 2000000
set_option pp.structureInstances false

theorem runAtAudit_wp {g : AuditM α} (hg : PrefixPreserves AuditInv AuditSafe g)
    (index : Nat) (w : World) :
    ⦃fun h => ⌜AuditInv h w⌝⦄ runAtPrefix index w g
    ⦃post⟨fun out h => ⌜AuditInv h out.2⌝, fun _ h => ⌜AuditSafe h⌝⟩⦄ :=
  runAtPrefix_wp (show PrefixEnsures AuditInv AuditSafe g (fun _ => AuditInv) from hg) index w

theorem audit_initial_prefill (trace : Trace) (w : World)
    (hr : Env.seccompPrefill trace.seccompPrefill
      (initialKernel trace.rlimit trace.net trace.bare trace.foreign trace.stepped trace.seccompChild)
        = .ok w.k) : AuditInv [] w := by
  have hi := allocation_initial trace.rlimit trace.net trace.bare trace.foreign
    trace.stepped trace.seccompChild
    { w with k := initialKernel trace.rlimit trace.net trace.bare trace.foreign trace.stepped trace.seccompChild } rfl
  exact audit_initial (allocation_prefill trace.seccompPrefill
    { w with k := initialKernel trace.rlimit trace.net trace.bare trace.foreign trace.stepped trace.seccompChild }
    w.k hi hr)

/-- The initialization and every concrete syscall discharge the state premise;
both WP branches retain safety, including failed prefill and end guards. -/
theorem executeTraceAudit_safe_wp (trace : Trace) (placeholders : Bool) :
    ⦃fun h => ⌜h = []⌝⦄ executeTraceAudit trace placeholders
    ⦃post⟨fun _ h => ⌜AuditSafe h⌝, fun _ h => ⌜AuditSafe h⌝⟩⦄ := by
  have syscall_spec (index : Nat) (w : World) (call : Syscall) :=
    runAtAudit_wp (syscallAudit_preserves call) index w
  have ambient_spec (index : Nat) (w : World) :=
    runAtAudit_wp (auditLift_kernel skipAmbient skipAmbient_sameKernel) index w
  unfold executeTraceAudit
  mvcgen [syscall_spec, ambient_spec]
  all_goals try exact
    ((post⟨fun out h => ⌜AuditInv h out.2.1⌝, fun _ h => ⌜AuditSafe h⌝⟩) :
      Invariant trace.ops.toList
        (World × Array Int × Array (Option (Nat × Nat)) × Array Json × Array Json × Array Json)
        (.except (Nat × Stop) (.arg (List AuditEvent) .pure)))
  all_goals try
    let r : Unit × World := by assumption
    exact ((post⟨fun _ h => ⌜AuditInv h r.2⌝, fun _ h => ⌜AuditSafe h⌝⟩) :
      Invariant r.2.steps.toList (Array Json)
        (.except (Nat × Stop) (.arg (List AuditEvent) .pure)))
  all_goals try
    let r : Unit × World := by assumption
    exact ((post⟨fun _ h => ⌜AuditInv h r.2⌝, fun _ h => ⌜AuditSafe h⌝⟩) :
      Invariant r.2.fired.toList (Array Json)
        (.except (Nat × Stop) (.arg (List AuditEvent) .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try trivial
  all_goals try (solve | rename_i history hi; exact AuditInv.kernel hi rfl)
  all_goals try exact AuditInv.safe (by assumption)
  all_goals try (solve | intros; assumption)
  all_goals try (solve | intros; exact AuditInv.safe (by assumption))
  all_goals
    rename_i history hh
    subst history
    first
    | exact audit_initial (allocation_initial trace.rlimit trace.net trace.bare trace.foreign
        trace.stepped trace.seccompChild _ rfl)
    | exact audit_initial_prefill trace _ (by assumption)
    | exact (audit_initial (allocation_initial trace.rlimit trace.net trace.bare trace.foreign
        trace.stepped trace.seccompChild
        { k := initialKernel trace.rlimit trace.net trace.bare trace.foreign trace.stepped trace.seccompChild,
          env := harnessEnv, timing := Env.timing } rfl)).safe

/-- Safety is unconditional in the original result: Stops preserve their reached
committed history and saved filter-entry validity just as successful JSON does. -/
theorem executeTraceAudit_safe (trace : Trace) (placeholders : Bool) :
    AuditSafe (runPrefixOuter (executeTraceAudit trace placeholders) []).2 := by
  have hs := (prefixOuter_wp_iff _ _ _ _).mp
    (executeTraceAudit_safe_wp trace placeholders) [] rfl
  cases hr : runPrefixOuter (executeTraceAudit trace placeholders) [] with
  | mk result hist => cases result <;> simpa only [hr] using hs

/-- Every reached saved filter entry is valid from initialized execution. Exact
filter order and early failure identify the evaluated prefix; certifying all
candidates does not assert that later candidates were evaluated. -/
theorem executeTraceAudit_trials (trace : Trace) (placeholders : Bool) :
    ∀ p ∈ probeEntries (runPrefixOuter (executeTraceAudit trace placeholders) []).2,
      AllocationInv p.history p.world ∧
      (p.world.suspended.filterM Env.Activation.consistent).run p.world =
        (p.world.suspended.filterM (fun a => activationTrialDecision a p.world p.history)).map
          (fun ys => (ys, p.world)) ∧
      ∀ a ∈ p.world.suspended,
        LifetimeEvent.Safe (runPrefix (activationRunPrefix a) p.world p.history).2 := by
  intro p hp
  exact savedProbe_trials (executeTraceAudit_safe trace placeholders).2 hp

end Leanux.Proofs.WG.Lifetimes
