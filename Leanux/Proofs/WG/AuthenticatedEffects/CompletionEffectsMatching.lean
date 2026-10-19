import Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffectsObservedProjection
import Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffectsFocus

/-! Natural matching into an existing combined journal, preserving all its
completion events rather than only a smaller filtered view. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffects
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity

variable (ρ : E → Option F)
  (eg : Completion.Event → E) (dg : E → Option Completion.Event)
  (et : Completion.Event → F) (dt : F → Option Completion.Event)
  (enc : ∀ e, ρ (eg e) = some (et e))
  (dec : ∀ e, dg e = (ρ e).bind dt)

include enc dec in
theorem focused_matching : Ops.Projects ρ (focused eg dg) (focused et dt) := by
  constructor
  all_goals intros
  all_goals exact focus_matching ρ eg dg et dt enc dec _

include enc dec in
theorem lifetimeBase_matching :
    LifetimeEffects.Ops.Projects ρ (lifetimeBase eg dg) (lifetimeBase et dt) := by
  have project {α} (action : MixedM α) : StateProjectsPrefix ρ id
      (focusStatePrefix (eg ∘ lifetimeEvent) (fun e => (dg e).bind lifetime?) action)
      (focusStatePrefix (et ∘ lifetimeEvent) (fun e => (dt e).bind lifetime?) action) :=
    state_focus_matching ρ _ _ _ _ (fun e => enc (lifetimeEvent e))
      (fun e => by rw [dec]; exact Option.bind_assoc _ _ _) action
  constructor
  all_goals intros
  all_goals exact project _

private theorem traversal_embedded (inverse : ∀ e, dt (et e) = some e) (pid : PeerId) :
    liftWGObserver (LifetimeEffects.traversalWith (lifetimeBase et dt) pid) =
      focusPrefix et dt (native.traversal pid) := by
  rw [show lifetimeBase et dt = LifetimeEffects.Ops.focus (et ∘ lifetimeEvent)
    (fun e => (dt e).bind lifetime?) LifetimeEffects.native from rfl]
  rw [LifetimeEffects.traversal_focus _ _ (fun e => by simp [Function.comp_def,inverse,lifetimeEvent,lifetime?,Completion.disposition?,TxDisposition.accessEvent])
    _ LifetimeEffects.native_appends]
  rw [lift_focus,← focus_composed]
  simp only [native,access_factor,lift_focus,← LifetimeEffects.traversal_factor]

private theorem dataSent_embedded (inverse : ∀ e, dt (et e) = some e) (pid : PeerId) :
    liftWGObserver (LifetimeEffects.dataSentWith (lifetimeBase et dt) pid) =
      focusPrefix et dt (native.dataSent pid) := by
  rw [show lifetimeBase et dt = LifetimeEffects.Ops.focus (et ∘ lifetimeEvent)
    (fun e => (dt e).bind lifetime?) LifetimeEffects.native from rfl]
  rw [LifetimeEffects.dataSent_focus _ _ (fun e => by simp [Function.comp_def,inverse,lifetimeEvent,lifetime?,Completion.disposition?,TxDisposition.accessEvent])
    _ LifetimeEffects.native_appends]
  rw [lift_focus,← focus_composed]
  simp only [native,access_factor,lift_focus,← LifetimeEffects.dataSent_factor]

private theorem fresh_embedded (inverse : ∀ e, dt (et e) = some e) (pid : PeerId) :
    liftWGObserver (LifetimeEffects.freshWith (lifetimeBase et dt) pid) =
      focusPrefix et dt (native.fresh pid) := by
  rw [show lifetimeBase et dt = LifetimeEffects.Ops.focus (et ∘ lifetimeEvent)
    (fun e => (dt e).bind lifetime?) LifetimeEffects.native from rfl]
  rw [LifetimeEffects.fresh_focus _ _ (fun e => by simp [Function.comp_def,inverse,lifetimeEvent,lifetime?,Completion.disposition?,TxDisposition.accessEvent])
    _ LifetimeEffects.native_appends]
  rw [lift_focus,← focus_composed]
  simp only [native,access_factor,lift_focus,← LifetimeEffects.fresh_factor]

include enc dec in
theorem observed_matching (inverse : ∀ e, dt (et e) = some e)
    (scope : E → Option (CausalScope.Event Cause))
    (arm : TimerEffects.Arm (CausalEffects.Context Cause) → E)
    (queue : TimerEffects.Queued (CausalEffects.Context Cause) → E)
    (armQuiet : ∀ r, ρ (arm r) = none) (queueQuiet : ∀ r, ρ (queue r) = none) :
    Ops.Projects ρ (observed eg dg scope arm queue) (focused et dt) := by
  have effects := LifetimeEffects.decorate_projects ρ _ _ (lifetimeBase_matching ρ eg dg et dt enc dec)
    scope arm queue armQuiet queueQuiet
  refine {focused_matching ρ eg dg et dt enc dec with traversal := ?_, dataSent := ?_, fresh := ?_}
  · intro pid
    have projected := (LifetimeEffects.traversal_projects ρ effects pid).liftWGObserver ρ id
    simpa only [observed,focused,traversal_embedded et dt inverse] using projected
  · intro pid
    have projected := (LifetimeEffects.dataSent_projects ρ effects pid).liftWGObserver ρ id
    simpa only [observed,focused,dataSent_embedded et dt inverse] using projected
  · intro pid
    have projected := (LifetimeEffects.fresh_projects ρ effects pid).liftWGObserver ρ id
    simpa only [observed,focused,fresh_embedded et dt inverse] using projected

include enc dec in
theorem observedStep_matching (inverse : ∀ e, dt (et e) = some e)
    (recordScope : CausalScope.Event Cause → E) (scope : E → Option (CausalScope.Event Cause))
    (cause : PeerId → List SkbId → Cause)
    (arm : TimerEffects.Arm (CausalEffects.Context Cause) → E)
    (queue : TimerEffects.Queued (CausalEffects.Context Cause) → E)
    (scopeQuiet : ∀ r, ρ (recordScope r) = none)
    (armQuiet : ∀ r, ρ (arm r) = none) (queueQuiet : ∀ r, ρ (queue r) = none) (pid : PeerId) :
    ProjectsPrefix ρ id (observedStep eg dg recordScope scope cause arm queue pid)
      (focusPrefix et dt (Completion.step pid)) := by
  rw [← step_focus et dt inverse]
  exact stepScoped_projects ρ recordScope cause scopeQuiet
    (observed_matching ρ eg dg et dt enc dec inverse scope arm queue armQuiet queueQuiet) pid

end Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffects
