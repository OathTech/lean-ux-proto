import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeProduct
import Leanux.Proofs.WG.AuthenticatedEffects.TimerEffectsReceipts

/-! Connect actual timer/queue receipts to the currently executing causal
scope. Missing or malformed context is recorded explicitly; native execution
is unchanged, and an initialized causal theorem must rule it out at effects. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalEffects
open Leanux Leanux.WG Leanux.Proofs.Logged

abbrev Context (Cause : Type) := Except CausalScope.Malformed (Option (CausalScope.Token Cause))

def atCurrent (decode : E → Option (CausalScope.Event Cause))
    (body : Context Cause → WGPrefix E α) : WGPrefix E α :=
  fun w a => ExceptT.mk fun h => runWGPrefix (body (CausalScope.current decode h)) w a h

theorem atCurrent_run (decode : E → Option (CausalScope.Event Cause))
    (body : Context Cause → WGPrefix E α) (w : WGWorld) (a : Ambient) (h : List E) :
    runWGPrefix (atCurrent decode body) w a h =
      runWGPrefix (body (CausalScope.current decode h)) w a h := rfl

theorem atCurrent_erases (decode : E → Option (CausalScope.Event Cause))
    (body : Context Cause → WGPrefix E α) (native : WG.M α)
    (erases : ∀ context, ErasesStatePrefix (body context) native) :
    ErasesStatePrefix (atCurrent decode body) native :=
  fun w a h => erases (CausalScope.current decode h) w a h

theorem atCurrent_projects (decode : E → Option (CausalScope.Event Cause))
    (body : Context Cause → WGPrefix E α) (ρ : E → Option F) (target : WGPrefix F α)
    (projects : ∀ context, StateProjectsPrefix ρ id (body context) target) :
    StateProjectsPrefix ρ id (atCurrent decode body) target :=
  fun w a h => projects (CausalScope.current decode h) w a h

def ops (decode : E → Option (CausalScope.Event Cause))
    (recordArm : TimerEffects.Arm (Context Cause) → E)
    (recordQueue : TimerEffects.Queued (Context Cause) → E) : TimerEffects.Ops (WGPrefix E) :=
  TimerEffects.observed
    (fun pid timer delay caller => atCurrent decode fun context =>
      TimerEffects.armReceipt recordArm context pid timer delay caller)
    (fun pid => atCurrent decode fun context => TimerEffects.queueReceipt recordQueue context pid)

theorem ops_erases (decode : E → Option (CausalScope.Event Cause))
    (recordArm : TimerEffects.Arm (Context Cause) → E)
    (recordQueue : TimerEffects.Queued (Context Cause) → E) : TimerEffects.Ops.Erases (ops decode recordArm recordQueue) where
  step := erasesStatePrefix_lift
  arm := fun pid timer delay caller => atCurrent_erases decode _ _
    (fun context => (TimerEffects.receipts_erases recordArm recordQueue context).arm pid timer delay caller)
  append := fun pid => atCurrent_erases decode _ _
    (fun context => (TimerEffects.receipts_erases recordArm recordQueue context).append pid)

theorem ops_projects (decode : E → Option (CausalScope.Event Cause))
    (recordArm : TimerEffects.Arm (Context Cause) → E)
    (recordQueue : TimerEffects.Queued (Context Cause) → E)
    (ρ : E → Option F) (ha : ∀ r, ρ (recordArm r) = none) (hq : ∀ r, ρ (recordQueue r) = none) :
    TimerEffects.Ops.Projects ρ (ops decode recordArm recordQueue) TimerEffects.lifted where
  step := by
    intro α action w a h
    change ((action.run w).run a,h.filterMap ρ) =
      (((action.run w).run a).map (fun ((x,v),b) => ((x,v),b)),h.filterMap ρ)
    cases (action.run w).run a <;> rfl
  arm := fun pid timer delay caller => atCurrent_projects decode _ ρ _
    (fun context => (TimerEffects.receipts_projects ρ recordArm recordQueue context ha hq).arm pid timer delay caller)
  append := fun pid => atCurrent_projects decode _ ρ _
    (fun context => (TimerEffects.receipts_projects ρ recordArm recordQueue context ha hq).append pid)

/-- An effect immediately inside a well-formed scope uses that exact scope's
token. The body cannot replace it with another earlier admission or peer. -/
theorem current_scope (record : CausalScope.Event Cause → E)
    (decode : E → Option (CausalScope.Event Cause))
    (inverse : ∀ event, decode (record event) = some event)
    (body : Context Cause → WGPrefix E α) (w : WGWorld) (a : Ambient) (h : List E)
    (before : List (CausalScope.Token Cause))
    (ready : CausalScope.stack (h.filterMap decode) = .ok before)
    (token : CausalScope.Token Cause) :
    runWGPrefix (atCurrent decode body) w a (h ++ [record (.entered token)]) =
      runWGPrefix (body (.ok (some token))) w a (h ++ [record (.entered token)]) := by
  rw [atCurrent_run,CausalScope.current_entered record decode inverse h before ready token]

end Leanux.Proofs.WG.AuthenticatedEffects.CausalEffects
