import Leanux.Proofs.WG.AuthenticatedEffects.CausalSelectionTimer

/-! Ordinary event families preserve positional selector evidence. Work and
 timer entry are deliberately absent: their real source guards are required. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Selections
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity

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
      Driver.History.state_bind (emit_quiet (.scope (.exited h.length)) True.intro)
        (fun _ => Driver.History.state_pure result))) w a h hi

theorem state_enter (cause : Cause) (quiet : ∀ index, Quiet (.scope (.entered ⟨index,cause⟩))) :
    Driver.StateHistorySafe Safe (CausalScope.enterState Event.scope cause) := by
  intro w a h hi
  have good := hi.emit (quiet_checked (.scope (.entered ⟨h.length,cause⟩)) (quiet h.length) h)
  exact ⟨[.scope (.entered ⟨h.length,cause⟩)],rfl,good,good⟩

theorem state_leave (token : Nat) :
    Driver.StateHistorySafe Safe (CausalScope.leaveState Event.scope token) :=
  emit_quiet _ True.intro

theorem product_emit (event : Event) (quiet : Quiet event) :
    Driver.ProductHistorySafe Safe (emitPrefix event) := by
  intro w h hi
  have good := hi.emit (quiet_checked event quiet h)
  exact ⟨[event],rfl,good,good⟩

theorem product_enter (cause : Cause) (quiet : ∀ index, Quiet (.scope (.entered ⟨index,cause⟩))) :
    Driver.ProductHistorySafe Safe (CausalScope.enterPrefix Event.scope cause) := by
  intro w h hi
  have good := hi.emit (quiet_checked (.scope (.entered ⟨h.length,cause⟩)) (quiet h.length) h)
  exact ⟨[.scope (.entered ⟨h.length,cause⟩)],rfl,good,good⟩

theorem product_leave (token : Nat) :
    Driver.ProductHistorySafe Safe (CausalScope.leavePrefix Event.scope token) :=
  product_emit _ True.intro

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

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Selections
