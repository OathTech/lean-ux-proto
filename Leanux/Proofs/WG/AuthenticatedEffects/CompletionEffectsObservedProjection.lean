import Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffectsNative

/-! The concrete causal completion observer projects to the existing complete
socket/disposition journal, including all events before an internal Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffects
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity

theorem lifetimeBase_projects (encode : Completion.Event → E) (decode : E → Option Completion.Event)
    (inverse : ∀ event, decode (encode event) = some event) :
    LifetimeEffects.Ops.Projects decode (lifetimeBase encode decode)
      (LifetimeEffects.Ops.focus lifetimeEvent lifetime? LifetimeEffects.native) := by
  have project {α} (action : MixedM α) : StateProjectsPrefix decode id
      (focusStatePrefix (encode ∘ lifetimeEvent) (fun e => (decode e).bind lifetime?) action)
      (focusStatePrefix lifetimeEvent lifetime? action) :=
    state_focus_matching decode _ _ _ _ (fun e => inverse (lifetimeEvent e)) (fun _ => rfl) action
  constructor
  all_goals intros
  all_goals exact project _

theorem observed_projects (encode : Completion.Event → E) (decode : E → Option Completion.Event)
    (inverse : ∀ event, decode (encode event) = some event)
    (scope : E → Option (CausalScope.Event Cause))
    (arm : TimerEffects.Arm (CausalEffects.Context Cause) → E)
    (queue : TimerEffects.Queued (CausalEffects.Context Cause) → E)
    (armQuiet : ∀ r, decode (arm r) = none) (queueQuiet : ∀ r, decode (queue r) = none) :
    Ops.Projects decode (observed encode decode scope arm queue) native := by
  have effects := LifetimeEffects.decorate_projects decode _ _ (lifetimeBase_projects encode decode inverse)
    scope arm queue armQuiet queueQuiet
  refine {focused_projects encode decode inverse with traversal := ?_, dataSent := ?_, fresh := ?_}
  · intro pid
    have projected := (LifetimeEffects.traversal_projects decode effects pid).liftWGObserver decode id
    simpa only [observed,native,LifetimeEffects.traversal_focus lifetimeEvent lifetime? (fun _ => rfl)
      LifetimeEffects.native LifetimeEffects.native_appends,
      ← LifetimeEffects.traversal_factor,← access_factor] using projected
  · intro pid
    have projected := (LifetimeEffects.dataSent_projects decode effects pid).liftWGObserver decode id
    simpa only [observed,native,LifetimeEffects.dataSent_focus lifetimeEvent lifetime? (fun _ => rfl)
      LifetimeEffects.native LifetimeEffects.native_appends,
      ← LifetimeEffects.dataSent_factor,← access_factor] using projected
  · intro pid
    have projected := (LifetimeEffects.fresh_projects decode effects pid).liftWGObserver decode id
    simpa only [observed,native,LifetimeEffects.fresh_focus lifetimeEvent lifetime? (fun _ => rfl)
      LifetimeEffects.native LifetimeEffects.native_appends,
      ← LifetimeEffects.fresh_factor,← access_factor] using projected

/-- The added lexical scope and actual causal effect receipts preserve every
original packet, lifetime, socket and disposal receipt on the same execution. -/
theorem observedStep_projects (encode : Completion.Event → E) (decode : E → Option Completion.Event)
    (inverse : ∀ event, decode (encode event) = some event)
    (recordScope : CausalScope.Event Cause → E) (scope : E → Option (CausalScope.Event Cause))
    (cause : PeerId → List SkbId → Cause)
    (arm : TimerEffects.Arm (CausalEffects.Context Cause) → E)
    (queue : TimerEffects.Queued (CausalEffects.Context Cause) → E)
    (scopeQuiet : ∀ r, decode (recordScope r) = none)
    (armQuiet : ∀ r, decode (arm r) = none) (queueQuiet : ∀ r, decode (queue r) = none)
    (pid : PeerId) :
    ProjectsPrefix decode id (observedStep encode decode recordScope scope cause arm queue pid)
      (Completion.step pid) :=
  stepScoped_projects decode recordScope cause scopeQuiet
    (observed_projects encode decode inverse scope arm queue armQuiet queueQuiet) pid

end Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffects
