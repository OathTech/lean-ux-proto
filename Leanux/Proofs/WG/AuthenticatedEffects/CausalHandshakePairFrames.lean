import Leanux.Proofs.WG.AuthenticatedEffects.CausalHandshakePairs

/-! Quiet native calls, non-handshake scopes and effect receipts preserve the
physical handshake-entry/callback adjacency relation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.HandshakePairs
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity

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
  have good := hi.emit (.scope (.entered ⟨h.length,cause⟩)) (quiet h.length)
  exact ⟨[.scope (.entered ⟨h.length,cause⟩)],rfl,good,good⟩

theorem state_leave (token : Nat) :
    Driver.StateHistorySafe Safe (CausalScope.leaveState Event.scope token) :=
  emit_quiet _ rfl

theorem product_emit (event : Event) (quiet : Quiet event) :
    Driver.ProductHistorySafe Safe (emitPrefix event) := by
  intro w h hi
  have good := hi.emit event quiet
  exact ⟨[event],rfl,good,good⟩

theorem product_enter (cause : Cause) (quiet : ∀ index, Quiet (.scope (.entered ⟨index,cause⟩))) :
    Driver.ProductHistorySafe Safe (CausalScope.enterPrefix Event.scope cause) := by
  intro w h hi
  have good := hi.emit (.scope (.entered ⟨h.length,cause⟩)) (quiet h.length)
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



theorem receipt_callback (record : HandshakeCausal.Event → Event)
    (kind : HandshakeCausal.Kind) (pid : PeerId) (body : WGPrefix Event α)
    (receipt : WGRunWitness α → Event) :
    receiptWGObserved (HandshakeWorker.callback record kind pid body) receipt =
      HandshakeWorker.callback record kind pid (receiptWGObserved body receipt) := by
  funext w a h
  rfl


/-- The protected entry and its first receipt are emitted before any stopping
body instruction; nested callbacks may then append their own paired scopes. -/
theorem product_scoped_pair (cause : Cause) (callback : Event)
    (needed : ∀ index, required (.scope (.entered ⟨index,cause⟩)) = some callback)
    (quiet : Quiet callback) (body : PrefixM Event α)
    (preserves : Driver.ProductHistorySafe Safe body) :
    Driver.ProductHistorySafe Safe (CausalScope.prefixScope Event.scope cause
      (fun _ => emitPrefix callback >>= fun _ => body)) := by
  intro w h hi
  let token : CausalScope.Token Cause := ⟨h.length,cause⟩
  let entered := h ++ [.scope (.entered token),callback]
  have ready : Safe entered := hi.pair_events _ callback (needed h.length) quiet
  obtain ⟨suffix,grown,safe,normal⟩ := preserves w entered ready
  clear normal
  change ∃ suffix, (runPrefix _ w h).2 = h ++ suffix ∧ _
  rw [CausalScope.prefix_run,runPrefix_bind,runPrefix_emit]
  simp only [List.append_assoc,List.singleton_append]
  cases run : runPrefix body w entered with
  | mk result history =>
    rw [run] at grown safe
    change history = entered ++ suffix at grown
    cases result with
    | error stop =>
      exact ⟨[.scope (.entered token),callback] ++ suffix,
        by simpa only [entered,List.append_assoc] using grown,safe,True.intro⟩
    | ok result =>
      rcases result with ⟨value,v⟩
      have closed := safe.emit (.scope (.exited h.length)) rfl
      exact ⟨[.scope (.entered token),callback] ++ suffix ++ [.scope (.exited h.length)],
        by simp only [grown,entered,List.append_assoc],closed,closed⟩

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.HandshakePairs
