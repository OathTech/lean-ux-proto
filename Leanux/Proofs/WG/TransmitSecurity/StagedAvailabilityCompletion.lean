import Leanux.Proofs.WG.HandshakeSecurity.StagedAvailableWorkers
import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityLifetime
import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityFocusedProduct

/-! Staged origins through the final journal's actual TX completion.
Every packet read and socket receipt remains in the same source execution;
transmit authorization and completion-item ancestry are separate obligations. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do
open AuthenticatedEffects AuthenticatedEffects.CausalJournal Queues
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

private abbrev observed := HandshakeSecurity.StagedConservation.SendResult.decorate Event.sendResult
  (CompletionEffects.observed
    (Event.old ∘ Journal.completionEvent) completion? scope? Event.armed Event.queued)

private theorem old (body : PrefixM Completion.Event α) (native : WG.M α)
    (erases : ErasesPrefix body (liftWG native)) (safe : ∀ h, Preserves (Inv h) native) :
    ProductSafe (focusPrefix (Event.old ∘ Journal.completionEvent) completion? body) :=
  product_quiet (Appends.focus _ _ _)
    (focusPrefix_other _ _ allocation? (fun event => by cases event <;> rfl) _)
    (focusPrefix_erases _ _ erases) (fun h => Native.product native (safe h))

private theorem access (body : MixedM α) (native : WG.M α)
    (erases : ErasesStatePrefix body native) (safe : ∀ h, Preserves (Inv h) native) :
    ProductSafe (focusPrefix (Event.old ∘ Journal.completionEvent) completion? (Completion.access body)) :=
  old _ native (Completion.access_erases erases) safe

private theorem peer (pid : PeerId) : ProductSafe
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion? (Completion.access (getPeerMixed pid))) :=
  access _ _ (getPeerMixed_erases pid) (fun _ => Native.read_peer pid)

private theorem packet (id : SkbId) : ProductSafe
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion? (Completion.access (getTxSkbPrefix id))) :=
  access _ _ (getTxSkbPrefix_erases id) (fun _ => Native.skb (SkbStore.getTx id))

private theorem modify_peer (pid : PeerId) (f : Peer → Peer)
    (same : ∀ p, (f p).internalId = p.internalId ∧ (f p).staged = p.staged) : ProductSafe
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion? (Completion.access (modifyPeerKeysPrefix pid f))) :=
  access _ _ (modifyPeerKeysPrefix_erases pid f) (fun _ => Native.update_peer pid f same)

private theorem sent (pid : PeerId) : ProductSafe
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion?
      (Completion.access (timersAnyAuthenticatedPacketSentPrefix pid))) :=
  access _ _ (timersAnyAuthenticatedPacketSentPrefix_erases pid) (fun _ => Native.delete_timer pid .sendKeepalive)

private theorem send (pid : PeerId) (id : SkbId) (packet : RunWitness DataPacket) : ProductSafe
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion? (Completion.send pid id packet)) :=
  old _ _ (Completion.send_erases pid id packet) (fun _ => Native.send_skb pid packet.value.bytes packet.value.ds)

private theorem drop (pid : PeerId) (item : List SkbId) : ProductSafe
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion?
      (focusPrefix Completion.Event.disposition Completion.disposition? (TxDisposition.drop pid item))) :=
  old _ _ (focusPrefix_erases _ _ (TxDisposition.drop_erases pid item)) (fun _ => Native.drop_completion pid)

private theorem dispose (pid : PeerId) (item : List SkbId) (key : KeypairId) : ProductSafe
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion?
      (focusPrefix Completion.Event.disposition Completion.disposition? (TxDisposition.dispose pid item key))) :=
  old _ _ (focusPrefix_erases _ _ (TxDisposition.dispose_erases pid item key)) (fun _ => Native.dispose_completion pid item key)

private theorem native (action : WG.M α) (safe : ∀ h, Preserves (Inv h) action) : ProductSafe
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion? (liftPrefix (liftWG action))) :=
  old _ _ (erasesPrefix_lift _) safe

private theorem emitted (event : Completion.Event) : ProductSafe
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion? (emitPrefix event)) := by
  intro w h hi
  have quiet : allocation? (Event.old (Journal.completionEvent event)) = none := by cases event <;> rfl
  have safe := hi.2.emit (quiet_event quiet)
  refine ⟨[Event.old (Journal.completionEvent event)],?_,?_,?_⟩
  · change h ++ (((h.filterMap completion? ++ [event]).drop (h.filterMap completion?).length).map
      (Event.old ∘ Journal.completionEvent)) = _
    simp only [List.drop_append_length,List.map_cons,List.map_nil,Function.comp_apply]
  · change Safe (h ++ (((h.filterMap completion? ++ [event]).drop (h.filterMap completion?).length).map (Event.old ∘ Journal.completionEvent)))
    simpa only [List.drop_append_length,List.map_cons,List.map_nil,Function.comp_apply] using safe
  · change Carrier (h ++ (((h.filterMap completion? ++ [event]).drop (h.filterMap completion?).length).map (Event.old ∘ Journal.completionEvent))) w.wg
    simpa only [Carrier,List.drop_append_length,List.map_cons,List.map_nil,Function.comp_apply] using And.intro (hi.1.append (fun _ e member => no_use (by
      have equal := List.mem_singleton.mp member
      subst e
      exact quiet))) safe

private theorem result_receipt (body : PrefixM Event α) (safe : ProductSafe body)
    (record : RunWitness α → Event) (quiet : ∀ r, allocation? (record r) = none) :
    ProductSafe (receiptObserved body record) := by
  unfold receiptObserved
  exact product_bind (product_capture _ safe) (fun r =>
    product_bind (product_emit (record r) (quiet r)) (fun _ => product_pure r.value))

open Lean Meta Elab Tactic in
elab "available_completion_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``ProductSafe do throwError "not a staged-availability product contract"
  let some action := target.getAppArgs.back? | throwError "missing action"
  let action := action.consumeMData.headBeta
  unless action.isAppOf ``focusPrefix do throwError "not a focused completion callback"
  let some body := action.getAppArgs.back? | throwError "missing focused body"
  let body := body.consumeMData.headBeta
  let body ← if body.isAppOf ``Completion.access || body.isAppOf ``focusPrefix then
      match body.getAppArgs.back? with
      | some inner => pure inner.consumeMData.headBeta
      | none => throwError "missing completion body"
    else pure body
  let .const actual _ := body.getAppFn | throwError "not a constant callback"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do throwError "different callback"

macro "available_completion_step" : tactic => `(tactic| first
  | (available_origin_product_head receiptObserved; refine result_receipt _ ?_ _ (fun _ => rfl))
  | (available_completion_head getPeerMixed; exact peer _)
  | (available_completion_head getTxSkbPrefix; exact packet _)
  | (available_completion_head modifyPeerKeysPrefix; apply modify_peer; intro p; exact ⟨rfl,rfl⟩)
  | (available_completion_head timersAnyAuthenticatedPacketSentPrefix; exact sent _)
  | (available_completion_head Completion.send; exact send _ _ _)
  | (available_completion_head TxDisposition.drop; exact drop _ _)
  | (available_completion_head TxDisposition.dispose; exact dispose _ _ _)
  | (available_completion_head emitPrefix; exact emitted _)
  | (available_completion_head liftPrefix
     apply native
     intro history
     repeat' first
       | (rx_retention_head PrevQueue.peek; exact Native.store (prevQueuePeek_sameWGStore _))
       | staged_available_native)
  | (available_origin_product_head liftWGPrefix
     apply product_state
     apply state_lift
     intro history
     repeat' first
       | (rx_retention_head PrevQueue.peek; exact Native.store (prevQueuePeek_sameWGStore _))
       | staged_available_native)
  | (available_origin_product_head LifetimeEffects.traversalWith; exact product_state (lifetime_traversal _))
  | (available_origin_product_head LifetimeEffects.dataSentWith; exact product_state (lifetime_data_sent _))
  | (available_origin_product_head LifetimeEffects.freshWith; exact product_state (lifetime_fresh _))
  | available_origin_product_step)

private theorem complete (pid : PeerId) (item : List SkbId) :
    ProductSafe (CompletionEffects.completeWith observed pid item) := by
  unfold CompletionEffects.completeWith TxDisposition.andObs
  simp only [observed,HandshakeSecurity.StagedConservation.SendResult.decorate,HandshakeSecurity.StagedConservation.SendResult.observed,CompletionEffects.observed,CompletionEffects.focused,CompletionEffects.native]
  repeat' available_completion_step

private theorem complete_scope (pid : PeerId) (item : List SkbId) : ProductSafe
    (CompletionEffects.completeScoped Event.scope CausalSources.Cause.completion observed pid item) :=
  product_scope (.completion pid item) _ (fun _ => complete pid item)

private theorem body (pid : PeerId) (first : Option (List SkbId)) : ProductSafe
    (CompletionEffects.bodySourceWith observed
      (CompletionEffects.completeScoped Event.scope CausalSources.Cause.completion observed) pid first) := by
  unfold CompletionEffects.bodySourceWith TxDisposition.andObs
  simp only [observed,HandshakeSecurity.StagedConservation.SendResult.decorate,HandshakeSecurity.StagedConservation.SendResult.observed,CompletionEffects.observed,CompletionEffects.focused,CompletionEffects.native]
  repeat' first
    | (available_origin_product_head CompletionEffects.completeScoped; exact complete_scope _ _)
    | available_completion_step

theorem transmit (pid : PeerId) : ProductSafe (CausalJournal.transmit pid) := by
  unfold CausalJournal.transmit CompletionEffects.stepScoped CompletionEffects.stepSourceWith
  simp only [HandshakeSecurity.StagedConservation.SendResult.decorate,HandshakeSecurity.StagedConservation.SendResult.observed,CompletionEffects.observed,CompletionEffects.focused,CompletionEffects.native]
  repeat' first
    | (available_origin_product_head CompletionEffects.bodySourceWith; exact body _ _)
    | available_completion_step

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
