import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialExecution

/-! Non-replay, non-confirmation event families preserve the RX security
history by their actual appended suffix. State preservation is separate. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Execution
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues AuthenticatedEffects Responder TransmitSecurity

theorem history_focus_product (encode : F → Journal.Event) (decode : Journal.Event → Option F)
    (quiet : ∀ e, Quiet (encode e)) (action : PrefixM F α) :
    Driver.ProductHistorySafe Safe (focusPrefix encode decode action) := by
  intro w h hi
  let suffix := ((runPrefix action w (h.filterMap decode)).2.drop
    (h.filterMap decode).length).map encode
  have safe : Safe (h ++ suffix) := hi.quiet (by
    intro e member
    obtain ⟨source,_,rfl⟩ := List.mem_map.mp member
    exact quiet source)
  refine ⟨suffix,rfl,safe,?_⟩
  cases (runPrefix (focusPrefix encode decode action) w h).1 with
  | error err => trivial
  | ok out => exact safe

theorem history_focus_state (encode : F → Journal.Event) (decode : Journal.Event → Option F)
    (quiet : ∀ e, Quiet (encode e)) (action : WGPrefix F α) :
    Driver.StateHistorySafe Safe (focusStatePrefix encode decode action) := by
  intro w a h hi
  let suffix := ((runStatePrefix action w a (h.filterMap decode)).2.drop
    (h.filterMap decode).length).map encode
  have safe : Safe (h ++ suffix) := hi.quiet (by
    intro e member
    obtain ⟨source,_,rfl⟩ := List.mem_map.mp member
    exact quiet source)
  refine ⟨suffix,rfl,safe,?_⟩
  cases (runPrefix ((focusStatePrefix encode decode action).run w) a h).1 with
  | error err => trivial
  | ok out => exact safe

theorem history_receipt_state (action : WGPrefix Journal.Event α)
    (make : WGRunWitness α → Journal.Event) (quiet : ∀ r, Quiet (make r))
    (safe : Driver.StateHistorySafe Safe action) :
    Driver.StateHistorySafe Safe (receiptWGObserved action make) := by
  intro w a h hi
  obtain ⟨suffix,appended,kept,_⟩ := safe w a h hi
  have equation := runWGPrefix_receiptWGObserved action make w a h
  unfold runWGPrefix runStatePrefix at equation
  rw [equation]
  cases run : runPrefix (action.run w) a h with
  | mk result hist =>
    simp only [run] at appended kept
    cases result with
    | error err => exact ⟨suffix,appended,kept,trivial⟩
    | ok out =>
      obtain ⟨⟨value,v⟩,b⟩ := out
      have after := kept.quiet (suffix := [make ⟨value,w,v,a,b⟩]) (by simpa using quiet ⟨value,w,v,a,b⟩)
      exact ⟨suffix ++ [make ⟨value,w,v,a,b⟩],by simp [appended],after,after⟩

theorem history_receipt_product (action : PrefixM Journal.Event α)
    (make : RunWitness α → Journal.Event) (quiet : ∀ r, Quiet (make r))
    (safe : Driver.ProductHistorySafe Safe action) :
    Driver.ProductHistorySafe Safe (receiptObserved action make) := by
  intro w h hi
  obtain ⟨suffix,appended,kept,_⟩ := safe w h hi
  rw [runPrefix_receiptObserved]
  cases run : runPrefix action w h with
  | mk result hist =>
    simp only [run] at appended kept
    cases result with
    | error err => exact ⟨suffix,appended,kept,trivial⟩
    | ok out =>
      obtain ⟨value,v⟩ := out
      have after := kept.quiet (suffix := [make ⟨value,w,v⟩]) (by simpa using quiet ⟨value,w,v⟩)
      exact ⟨suffix ++ [make ⟨value,w,v⟩],by simp [appended],after,after⟩

theorem history_lower (action : PrefixM Journal.Event α)
    (safe : Driver.ProductHistorySafe Safe action) :
    Driver.StateHistorySafe Safe (NativeAdapter.lower action) := by
  intro w a h hi
  obtain ⟨suffix,appended,kept,_⟩ := safe (NativeAdapter.world w a) h hi
  refine ⟨suffix,appended,kept,?_⟩
  cases (runPrefix ((NativeAdapter.lower action).run w) a h).1 with
  | error err => trivial
  | ok out => exact kept

theorem prepare : ProductSafe (Journal.hooks.prepare) := by
  have observed : PrefixPreserves (fun h w => Bounded (h.filterMap Journal.origin?) w.wg)
      (fun _ => True) Journal.hooks.prepare :=
    ((bounded_prepare.liftWGObserver).focus Journal.Event.rxOrigin Journal.origin? (fun _ => rfl)).preserves
  have history := history_focus_product Journal.Event.rxOrigin Journal.origin?
    (fun _ => ⟨rfl,by intro pid kid r impossible; cases impossible⟩) (liftWGObserver RxOrigin.prepare)
  intro w h hi
  obtain ⟨suffix,appended,_,normal⟩ := observed w h hi.1
  obtain ⟨_,_,safe,_⟩ := history w h hi.2
  refine ⟨suffix,appended,safe,?_⟩
  cases run : (runPrefix Journal.hooks.prepare w h).1 with
  | error err => trivial
  | ok out =>
    obtain ⟨value,v⟩ := out
    exact ⟨by simpa only [run] using normal,safe⟩

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Execution
