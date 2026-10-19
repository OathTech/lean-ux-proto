import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilitySource
import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeContracts

/-! Native observation adapters carry live birth credits only across
histories proved to contain no TX allocation. Actual allocation is separate. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects AuthenticatedEffects.CausalJournal

theorem state_capture {action : WGPrefix Event α} (safe : StateSafe action) :
    StateSafe (captureWGObserved action) := StatePrefixPreserves.captureWGObserved safe

theorem state_receipt {action : WGPrefix Event α} (safe : StateSafe action)
    (record : WGRunWitness α → Event) (quiet : ∀ r, allocation? (record r) = none) :
    StateSafe (receiptWGObserved action record) :=
  StatePrefixEnsures.bind (state_capture safe) (fun r =>
    StatePrefixEnsures.bind (state_emit (record r) (quiet r)) (fun _ => state_pure r.value))

theorem state_current (body : Context → WGPrefix Event α) (safe : ∀ context, StateSafe (body context)) :
    StateSafe (AuthenticatedEffects.CausalEffects.atCurrent scope? body) := by
  intro w a h before
  exact safe (AuthenticatedEffects.CausalScope.current scope? h) w a h before

/-- A native frame and a separately proved history contract compose without
requiring an invariant at arbitrary observer callback arguments. -/
theorem state_history {action : WGPrefix Event α} {native : WG.M α}
    (history : Driver.StateHistorySafe Safe action) (erase : ErasesStatePrefix action native)
    (kept : ∀ h, Preserves (Inv h) native)
    (quiet : StateHistoryFrame allocation? action) : StateSafe action := by
  intro w a h before
  obtain ⟨suffix,position,safe,_⟩ := history w a h before.2
  refine ⟨suffix,position,safe,?_⟩
  cases outcome : (runPrefix (action.run w) a h).1 with
  | error stop => trivial
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    have run : (native.run w).run a = .ok ((value,v),b) := (erase w a h).symm.trans outcome
    have inv := (hoare_iff_run_ambient _ _ _).mp (kept h) w a value v b before.1 run
    refine ⟨?_,safe⟩
    rw [position]
    exact inv.append (fun _ event member => no_use (suffix_quiet quiet position event member))

theorem state_scope (cause : Cause) (body : WGPrefix Event α) (safe : StateSafe body) :
    StateSafe (CausalScope.scope Event.scope cause body) :=
  CausalScope.scope_preserves Event.scope cause body (fun _ _ _ before => before.2)
    (fun event _ _ _ before => ⟨before.1.append (quiet_singleton rfl),before.2.emit (quiet_event (event := .scope event) rfl)⟩) safe

theorem state_bind {body : WGPrefix Event α} {next : α → WGPrefix Event β}
    (safe : StateSafe body) (tail : ∀ value, StateSafe (next value)) : StateSafe (body >>= next) :=
  StatePrefixEnsures.bind safe tail

theorem state_ite (p : Prop) [Decidable p] {left right : WGPrefix Event α}
    (hl : p → StateSafe left) (hr : ¬ p → StateSafe right) : StateSafe (if p then left else right) := by
  by_cases hp : p <;> simp only [hp,↓reduceIte]
  · exact hl hp
  · exact hr hp

theorem state_forIn {α β : Type} (xs : List α) (initial : β) (body : α → β → WGPrefix Event (ForInStep β))
    (safe : ∀ value acc, StateSafe (body value acc)) : StateSafe (forIn xs initial body) :=
  StatePrefixEnsures.forInInvariant xs initial body (fun _ h w _ => Carrier h w) Safe
    (fun _ _ _ _ before => before.2) safe


end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
