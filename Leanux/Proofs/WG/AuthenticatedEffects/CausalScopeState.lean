import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeContracts

/-! Split entry/exit callbacks for a native-WireGuard lexical scope. They are
used at an already identified source cut; recording a cause does not prove it
authorized. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalScope
open Leanux Leanux.Proofs.Logged

def enterState (record : Event Cause → E) (cause : Cause) : WGPrefix E Nat :=
  fun w a => ExceptT.mk fun h =>
    (.ok ((h.length,w),a),h ++ [record (.entered ⟨h.length,cause⟩)])

def leaveState (record : Event Cause → E) (position : Nat) : WGPrefix E Unit :=
  emitStatePrefix (record (.exited position))

theorem enterState_projects (record : Event Cause → E) (cause : Cause) (ρ : E → Option F)
    (quiet : ∀ event, ρ (record event) = none) :
    StateProjectsPrefix ρ (fun _ => 0) (enterState record cause) (pure 0) := by
  intro w a h
  change (Except.ok (ε := Stop) ((0,w),a),h.filterMap ρ) =
    (Except.ok (ε := Stop) ((0,w),a),(h ++ [record (.entered ⟨h.length,cause⟩)]).filterMap ρ)
  simp only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,quiet,List.append_nil]

theorem leaveState_projects (record : Event Cause → E) (position : Nat) (ρ : E → Option F)
    (quiet : ∀ event, ρ (record event) = none) :
    StateProjectsPrefix ρ id (leaveState record position) (pure ()) := by
  intro w a h
  change (Except.ok (ε := Stop) (((),w),a),h.filterMap ρ) =
    (Except.ok (ε := Stop) (((),w),a),(h ++ [record (.exited position)]).filterMap ρ)
  simp only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,quiet,List.append_nil]

theorem enterState_preserves {P : List E → WGWorld → Ambient → Prop} {S : List E → Prop}
    (record : Event Cause → E) (cause : Cause)
    (safe : ∀ h w a, P h w a → S h)
    (markers : ∀ event h w a, P h w a → P (h ++ [record event]) w a) :
    StatePrefixPreserves P S (enterState record cause) := by
  intro w a h hi
  exact ⟨[record (.entered ⟨h.length,cause⟩)],rfl,
    safe _ _ _ (markers (.entered ⟨h.length,cause⟩) _ _ _ hi),
    markers (.entered ⟨h.length,cause⟩) _ _ _ hi⟩

theorem leaveState_preserves {P : List E → WGWorld → Ambient → Prop} {S : List E → Prop}
    (record : Event Cause → E) (position : Nat)
    (safe : ∀ h w a, P h w a → S h)
    (markers : ∀ event h w a, P h w a → P (h ++ [record event]) w a) :
    StatePrefixPreserves P S (leaveState record position) :=
  StatePrefixEnsures.emit _
    (fun h w a hi => safe _ _ _ (markers (.exited position) h w a hi))
    (fun h w a hi => markers (.exited position) h w a hi)

end Leanux.Proofs.WG.AuthenticatedEffects.CausalScope
