import Leanux.Proofs.WG.AuthenticatedEffects.DelayedObservedCarrier
import Leanux.Proofs.WG.AuthenticatedEffects.CausalJournalSource
import Leanux.Proofs.WG.AuthenticatedEffects.TimerSendFrames
import Leanux.Proofs.WG.AuthenticatedEffects.SendQueueReceiverFrames

/-! State contracts for the final journal's live timer and queued-work
occurrences. Native frames preserve just these projections; scopes themselves
mint no delayed-effect occurrence and grant no authorization. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do

abbrev Inv := DelayedEffects.Inv Event.armed Event.queued
abbrev StateSafe (body : WGPrefix Event α) :=
  StatePrefixPreserves (fun h w _ => Inv h w) (fun _ => True) body
abbrev ProductSafe (body : PrefixM Event α) :=
  PrefixPreserves (fun h w => Inv h w.wg) (fun _ => True) body

theorem state_pure (value : α) : StateSafe (pure value) :=
  StatePrefixEnsures.pure _ (fun _ _ _ _ => True.intro) (fun _ _ _ hi => hi)

theorem state_native (action : WG.M α) (frame : ∀ h, Preserves (Inv h) action) :
    StateSafe (liftWGPrefix action) :=
  StatePrefixEnsures.lift _ (fun _ _ _ _ => True.intro)
    (fun h w a value v b hi run => (hoare_iff_run_ambient _ _ _).mp (frame h) w a value v b hi run)

theorem state_framed (action : WG.M α)
    (timers : ∀ initial, Preserves (TimerSlots.Retained initial) action)
    (work : SameView QueuedOccurrences.queue action) : StateSafe (liftWGPrefix action) :=
  state_native action (DelayedEffects.native_retained action timers work)

theorem state_observed (body : WGPrefix Event α) (native : WG.M α)
    (erases : ErasesStatePrefix body native) (appends : StateAppends body)
    (frame : ∀ h, Preserves (Inv h) native) : StateSafe body := by
  intro w a h hi
  obtain ⟨suffix,grown⟩ := appends w a h
  refine ⟨suffix,grown,True.intro,?_⟩
  cases run : (runPrefix (body.run w) a h).1 with
  | error stop => trivial
  | ok result =>
    rcases result with ⟨⟨value,v⟩,b⟩
    have original := (erases w a h).symm.trans run
    have kept := (hoare_iff_run_ambient _ _ _).mp (frame h) w a value v b hi original
    rw [grown]
    exact kept.append suffix

theorem state_bind {body : WGPrefix Event α} {next : α → WGPrefix Event β}
    (preserves : StateSafe body) (tail : ∀ value, StateSafe (next value)) : StateSafe (body >>= next) :=
  StatePrefixEnsures.bind preserves tail

theorem state_ite (p : Prop) [Decidable p] {left right : WGPrefix Event α}
    (hl : p → StateSafe left) (hr : ¬ p → StateSafe right) : StateSafe (if p then left else right) := by
  by_cases hp : p <;> simp only [hp,↓reduceIte]
  · exact hl hp
  · exact hr hp

theorem state_forIn {α β : Type} (xs : List α) (initial : β) (body : α → β → WGPrefix Event (ForInStep β))
    (preserves : ∀ value state, StateSafe (body value state)) : StateSafe (forIn xs initial body) := by
  apply StatePrefixEnsures.forInInvariant xs initial (I := fun _ h w _ => Inv h w)
  · intro _ _ _ _ _; trivial
  · exact preserves

theorem state_scope (cause : Cause) (body : WGPrefix Event α) (preserves : StateSafe body) :
    StateSafe (CausalScope.scope Event.scope cause body) :=
  CausalScope.scope_preserves Event.scope cause body (fun _ _ _ _ => True.intro)
    (fun _ _ _ _ hi => hi.append _) preserves

theorem state_emit (event : Event) : StateSafe (emitStatePrefix event) :=
  StatePrefixEnsures.emit _ (fun _ _ _ _ => True.intro) (fun _ _ _ hi => hi.append _)

theorem state_receipt (body : WGPrefix Event α) (preserves : StateSafe body)
    (record : WGRunWitness α → Event) : StateSafe (receiptWGObserved body record) :=
  state_bind preserves.captureWGObserved (fun r => state_bind (state_emit (record r)) (fun _ => state_pure r.value))

theorem state_current (body : Context → WGPrefix Event α) (preserves : ∀ context, StateSafe (body context)) :
    StateSafe (CausalEffects.atCurrent scope? body) := by
  intro w a h hi
  exact preserves (CausalScope.current scope? h) w a h hi

theorem arm (pid : PeerId) (timer : PeerTimer) (delay : Nat) (caller : Option UInt64) :
    StateSafe (effects.arm pid timer delay caller) :=
  state_current _ (fun cause => DelayedEffects.arm_preserves Event.armed Event.queued cause pid timer delay caller)

theorem queue (pid : PeerId) : StateSafe (effects.append pid) :=
  state_current _ (fun cause => DelayedEffects.queue_preserves Event.armed Event.queued cause pid)

theorem delete (pid : PeerId) (timer : PeerTimer) : StateSafe (liftWGPrefix (delTimer pid timer)) :=
  DelayedEffects.delete_preserves Event.armed Event.queued pid timer

open Lean Meta Elab Tactic in
elab "causal_delayed_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``StateSafe || target.isAppOf ``ProductSafe do throwError "not a delayed carrier contract"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  let action := if action.isAppOf ``liftWGObserver then action.getAppArgs.back!.consumeMData else action
  let .const actual _ := action.getAppFn | throwError "not a constant-headed source"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do throwError "different source head"

macro "causal_delayed_step" : tactic => `(tactic| first
  | (causal_delayed_head Pure.pure; exact state_pure _)
  | (causal_delayed_head Bind.bind; apply state_bind)
  | (causal_delayed_head ite; apply state_ite)
  | (causal_delayed_head ForIn.forIn; apply state_forIn)
  | maintenance_intro
  | (split; all_goals try simp_all only []; all_goals try subst_vars)
  | simp +failIfUnchanged only [bind_assoc,pure_bind])

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
