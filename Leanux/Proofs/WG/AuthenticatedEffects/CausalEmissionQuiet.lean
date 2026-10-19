import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionDelivery
import Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrenceOriginPoll
import Leanux.Proofs.WG.TransmitSecurity.DriverEffectsHistory

/-! Independent delivery-history frames for callbacks which cannot emit a
delivery boundary. Native egress effects remain accounted by the separate
live carrier; these facts only retain prior pre-clear certificates. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions.Deliveries
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity

def delivery? : Event → Option (List SentDatagram)
  | .delivery sent => some sent
  | _ => none

def Quiet (event : Event) : Prop := delivery? event = none

theorem Safe.quiet (hi : Safe h) (quiet : ∀ event ∈ suffix, Quiet event) : Safe (h ++ suffix) := by
  apply hi.append
  intro pre event post position
  have allowed := quiet event (by rw [position]; simp)
  cases event <;> first | trivial | cases allowed

theorem Safe.quiet_emit {history : List Event} (safe : Safe history) (event : Event) (quiet : Quiet event) :
    Safe (history ++ [event]) := safe.quiet (by
  intro value member
  obtain rfl := List.mem_singleton.mp member
  exact quiet)

theorem emit_quiet (event : Event) (quiet : Quiet event) :
    Driver.StateHistorySafe Safe (emitStatePrefix event) :=
  StatePrefixEnsures.emit event (fun _ _ _ hi => hi.quiet_emit event quiet)
    (fun _ _ _ hi => hi.quiet_emit event quiet)

theorem receipt_quiet (body : WGPrefix Event α) (preserves : Driver.StateHistorySafe Safe body)
    (record : WGRunWitness α → Event) (quiet : ∀ r, Quiet (record r)) :
    Driver.StateHistorySafe Safe (receiptWGObserved body record) := by
  unfold receiptWGObserved
  exact Driver.History.state_bind preserves.captureWGObserved (fun r =>
    Driver.History.state_bind (emit_quiet (record r) (quiet r)) (fun _ => Driver.History.state_pure _))

theorem current_quiet (body : Context → WGPrefix Event α)
    (safe : ∀ context, Driver.StateHistorySafe Safe (body context)) :
    Driver.StateHistorySafe Safe (CausalEffects.atCurrent scope? body) := by
  intro w a h hi
  exact safe (CausalScope.current scope? h) w a h hi

theorem effects_safe : Driver.EffectsHistory Safe effects where
  step := Driver.History.state_lift
  arm := fun _ _ _ _ => current_quiet _ (fun _ =>
    receipt_quiet _ (Driver.History.state_lift _) _ (fun _ => rfl))
  append := fun _ => current_quiet _ (fun _ =>
    receipt_quiet _ (Driver.History.state_lift _) _ (fun _ => rfl))

theorem initiated (pid : PeerId) : Driver.StateHistorySafe Safe (TimerEffects.initiatedWith effects pid) := by
  unfold TimerEffects.initiatedWith
  repeat' effect_history_step effects_safe

theorem quiet_state (encode : F → Event) (decode : Event → Option F)
    (quiet : ∀ event, Quiet (encode event)) (body : WGPrefix F α) :
    Driver.StateHistorySafe Safe (focusStatePrefix encode decode body) := by
  intro w a h hi
  let suffix := ((runWGPrefix body w a (h.filterMap decode)).2.drop (h.filterMap decode).length).map encode
  have good : Safe (h ++ suffix) := hi.quiet (by
    intro event member
    obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
    exact quiet original)
  refine ⟨suffix,rfl,good,?_⟩
  cases (runPrefix (StateT.run (focusStatePrefix encode decode body) w) a h).1 <;> trivial

theorem quiet_product (encode : F → Event) (decode : Event → Option F)
    (quiet : ∀ event, Quiet (encode event)) (body : PrefixM F α) :
    Driver.ProductHistorySafe Safe (focusPrefix encode decode body) := by
  intro w h hi
  let suffix := ((runPrefix body w (h.filterMap decode)).2.drop (h.filterMap decode).length).map encode
  have good : Safe (h ++ suffix) := hi.quiet (by
    intro event member
    obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
    exact quiet original)
  refine ⟨suffix,rfl,good,?_⟩
  cases (runPrefix (focusPrefix encode decode body) w h).1 <;> trivial

theorem state_scope (cause : Cause) (quiet : ∀ index, Quiet (.scope (.entered ⟨index,cause⟩))) (body : WGPrefix Event α)
    (preserves : Driver.StateHistorySafe Safe body) :
    Driver.StateHistorySafe Safe (CausalScope.scope Event.scope cause body) := by
  intro w a h hi
  exact Driver.History.state_bind (emit_quiet (.scope (.entered ⟨h.length,cause⟩)) (quiet h.length))
    (fun _ => Driver.History.state_bind preserves (fun result =>
      Driver.History.state_bind (emit_quiet (.scope (.exited h.length)) rfl)
        (fun _ => Driver.History.state_pure result))) w a h hi

theorem state_enter (cause : Cause) (quiet : ∀ index, Quiet (.scope (.entered ⟨index,cause⟩))) :
    Driver.StateHistorySafe Safe (CausalScope.enterState Event.scope cause) := by
  intro w a h hi
  have good := hi.quiet_emit (.scope (.entered ⟨h.length,cause⟩)) (quiet h.length)
  exact ⟨[.scope (.entered ⟨h.length,cause⟩)],rfl,good,good⟩

theorem state_leave (token : Nat) :
    Driver.StateHistorySafe Safe (CausalScope.leaveState Event.scope token) :=
  emit_quiet _ rfl

theorem product_emit (event : Event) (quiet : Quiet event) :
    Driver.ProductHistorySafe Safe (emitPrefix event) := by
  intro w h hi
  have good := hi.quiet_emit event quiet
  exact ⟨[event],rfl,good,good⟩

theorem product_enter (cause : Cause) (quiet : ∀ index, Quiet (.scope (.entered ⟨index,cause⟩))) :
    Driver.ProductHistorySafe Safe (CausalScope.enterPrefix Event.scope cause) := by
  intro w h hi
  have good := hi.quiet_emit (.scope (.entered ⟨h.length,cause⟩)) (quiet h.length)
  exact ⟨[.scope (.entered ⟨h.length,cause⟩)],rfl,good,good⟩

theorem product_leave (token : Nat) :
    Driver.ProductHistorySafe Safe (CausalScope.leavePrefix Event.scope token) :=
  product_emit _ rfl

theorem product_scope (cause : Cause) (quiet : ∀ index, Quiet (.scope (.entered ⟨index,cause⟩))) (body : CausalScope.Token Cause → PrefixM Event α)
    (preserves : ∀ token, Driver.ProductHistorySafe Safe (body token)) :
    Driver.ProductHistorySafe Safe (CausalScope.prefixScope Event.scope cause body) := by
  intro w h hi
  exact Driver.History.product_bind (product_emit (.scope (.entered ⟨h.length,cause⟩)) (quiet h.length))
    (fun _ => Driver.History.product_bind (preserves ⟨h.length,cause⟩) (fun result =>
      Driver.History.product_bind (product_leave h.length) (fun _ => Driver.History.product_pure result))) w h hi

theorem derived (pid : PeerId) : Driver.StateHistorySafe Safe (TimerEffects.derivedWith effects pid) := by
  unfold TimerEffects.derivedWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  exact Driver.History.state_bind (Driver.effects_modify_history effects_safe _ _ _ _)
    (fun _ => Driver.History.state_pure _)


theorem protocol_send (pid : PeerId) (bytes : List UInt8) :
    Driver.StateHistorySafe Safe (ProtocolSocket.observed Event.protocolSocket scope? pid bytes) :=
  ProtocolSocket.observed_history Safe Event.protocolSocket scope?
    (fun _ _ _ hi _ => hi.quiet_emit _ rfl) pid bytes

theorem cookie_send (mac : HandshakeMac) (msg : List UInt8) (src : SkbSource) :
    Driver.StateHistorySafe Safe (CookieSocket.observed Event.cookieSocket mac msg src) :=
  CookieSocket.observed_history Safe Event.cookieSocket mac msg src (fun _ _ hi _ => hi.quiet_emit _ rfl)

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions.Deliveries
