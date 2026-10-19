import Leanux.Proofs.WG.AuthenticatedEffects.FixtureEffectsProjection
import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeState

/-! Concrete fixture scope callbacks with source trigger metadata. Their event
projection is transparent; final authorization still requires the shared driver
to place them at the exact fixture source sites. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.FixtureEffects
open Leanux Leanux.Proofs.Logged

def scopeHooks (record : CausalScope.Event Cause → E) (cause : Trigger → Cause) : Hooks E where
  enter := fun trigger => CausalScope.enterState record (cause trigger)
  leave := CausalScope.leaveState record

theorem run_scope (record : CausalScope.Event Cause → E) (cause : Trigger → Cause)
    (trigger : Trigger) (body : WGPrefix E α) :
    runWith (scopeHooks record cause) trigger body = CausalScope.scope record (cause trigger) body := by
  funext w a h
  rfl

theorem scope_projects (record : CausalScope.Event Cause → E) (cause : Trigger → Cause)
    (ρ : E → Option F) (quiet : ∀ event, ρ (record event) = none)
    (trigger : Trigger) (body : WGPrefix E α) (target : WGPrefix F α)
    (projects : StateProjectsPrefix ρ id body target) :
    StateProjectsPrefix ρ id (runWith (scopeHooks record cause) trigger body) target := by
  rw [run_scope]
  exact CausalScope.withToken_projects record (cause trigger) ρ quiet (fun _ => body) target
    (fun _ => projects)

theorem scope_entry (record : CausalScope.Event Cause → E) (cause : Trigger → Cause)
    (trigger : Trigger) (body : WGPrefix E α) (appends : StateAppends body)
    (w : WGWorld) (a : Ambient) (h : List E) :
    ∃ suffix, (runWGPrefix (runWith (scopeHooks record cause) trigger body) w a h).2 =
      h ++ record (.entered ⟨h.length,cause trigger⟩) :: suffix := by
  rw [run_scope]
  exact CausalScope.withToken_entry record (cause trigger) (fun _ => body) (fun _ => appends) w a h

end Leanux.Proofs.WG.AuthenticatedEffects.FixtureEffects
