import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedCompletionFrames
import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedLifetime

/-! Live delayed occurrences through the final journal's actual TX completion.
Every packet read and socket receipt remains in the same source execution;
transmit authorization and completion-item ancestry are separate obligations. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do
open TransmitSecurity Queues TimerSlots
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

private abbrev observed := completionOps

private theorem old (body : PrefixM Completion.Event α) (native : WG.M α)
    (erases : ErasesPrefix body (liftWG native)) (safe : StateSafe (liftWGPrefix native)) :
    ProductSafe (focusPrefix (Event.old ∘ Journal.completionEvent) completion? body) :=
  product_observed _ native (focusPrefix_erases _ _ erases) (Appends.focus _ _ _) safe

private theorem access (body : MixedM α) (native : WG.M α)
    (erases : ErasesStatePrefix body native) (safe : StateSafe (liftWGPrefix native)) :
    ProductSafe (focusPrefix (Event.old ∘ Journal.completionEvent) completion? (Completion.access body)) :=
  old _ native (Completion.access_erases erases) safe

private theorem peer (pid : PeerId) : ProductSafe
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion? (Completion.access (getPeerMixed pid))) :=
  access _ _ (getPeerMixed_erases pid) (by causal_delayed_native)

private theorem packet (id : SkbId) : ProductSafe
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion? (Completion.access (getTxSkbPrefix id))) :=
  access _ _ (getTxSkbPrefix_erases id) (skb (SkbStore.getTx id))

private theorem modify_peer (pid : PeerId) (f : Peer → Peer)
    (timers : ∀ p timer, ((f p).internalId,(f p).timer timer,(f p).wheel timer) =
      (p.internalId,p.timer timer,p.wheel timer)) : ProductSafe
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion? (Completion.access (modifyPeerKeysPrefix pid f))) :=
  access _ _ (modifyPeerKeysPrefix_erases pid f) (native_peer_update pid f timers)

private theorem sent (pid : PeerId) : ProductSafe
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion?
      (Completion.access (timersAnyAuthenticatedPacketSentPrefix pid))) :=
  access _ _ (timersAnyAuthenticatedPacketSentPrefix_erases pid) (delete pid .sendKeepalive)

private theorem send (pid : PeerId) (id : SkbId) (packet : RunWitness DataPacket) : ProductSafe
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion? (Completion.send pid id packet)) :=
  old _ _ (Completion.send_erases pid id packet) (send_skb pid packet.value.bytes packet.value.ds)

private theorem drop (pid : PeerId) (item : List SkbId) : ProductSafe
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion?
      (focusPrefix Completion.Event.disposition Completion.disposition? (TxDisposition.drop pid item))) :=
  old _ _ (focusPrefix_erases _ _ (TxDisposition.drop_erases pid item)) (drop_completion pid)

private theorem dispose (pid : PeerId) (item : List SkbId) (key : KeypairId) : ProductSafe
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion?
      (focusPrefix Completion.Event.disposition Completion.disposition? (TxDisposition.dispose pid item key))) :=
  old _ _ (focusPrefix_erases _ _ (TxDisposition.dispose_erases pid item key)) (dispose_completion pid item key)

private theorem actual_dispose (pid : PeerId) (item : List SkbId) (key : KeypairId) :
    ProductSafe (completionOps.dispose pid item key) :=
  product_observed _ _ (CallbackFrames.dispose_erases pid item key)
    (CallbackQuiet.dispose (fun _ : Event => (none : Option Empty)) (fun _ => rfl) (fun _ => rfl) pid item key).1
    (dispose_completion pid item key)

private theorem actual_dead (pid : PeerId) (item : List SkbId) (head : DataPacket) :
    ProductSafe (HandshakeSecurity.StagedConservation.Terminal.deadObserved
      txEvent txEvent? Event.stagedDisposal Event.terminalDrop pid item head) :=
  product_observed _ _ (CallbackFrames.dead_erases pid item head)
    (CallbackQuiet.dead (fun _ : Event => (none : Option Empty))
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) pid item head).1
    (dispose_completion pid item head.keypair)

private theorem native (action : WG.M α) (safe : StateSafe (liftWGPrefix action)) : ProductSafe
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion? (liftPrefix (liftWG action))) :=
  old _ _ (erasesPrefix_lift _) safe

private theorem emitted (event : Completion.Event) : ProductSafe
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion? (emitPrefix event)) := by
  intro w h hi
  refine ⟨[Event.old (Journal.completionEvent event)],?_,True.intro,?_⟩
  · change h ++ (((h.filterMap completion? ++ [event]).drop (h.filterMap completion?).length).map
      (Event.old ∘ Journal.completionEvent)) = _
    simp only [List.drop_append_length,List.map_cons,List.map_nil,Function.comp_apply]
  · exact hi.append _

open Lean Meta Elab Tactic in
elab "causal_delayed_completion_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``ProductSafe do throwError "not a delayed product contract"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  unless action.isAppOf ``focusPrefix do throwError "not a focused completion callback"
  let body := action.getAppArgs.back!.consumeMData.headBeta
  let body := if body.isAppOf ``Completion.access || body.isAppOf ``focusPrefix then
      body.getAppArgs.back!.consumeMData.headBeta else body
  let .const actual _ := body.getAppFn | throwError "not a constant callback"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do throwError "different callback"

private theorem result_receipt (body : PrefixM Event α) (safe : ProductSafe body)
    (record : RunWitness α → Event) : ProductSafe (receiptObserved body record) := by
  unfold receiptObserved
  exact product_bind (product_capture body safe) (fun r =>
    product_bind (product_emit (record r)) (fun _ => product_pure r.value))

macro "causal_delayed_completion_step" : tactic => `(tactic| first
  | (causal_delayed_head HandshakeSecurity.StagedDisposal.TxSource.dispose; exact actual_dispose _ _ _)
  | (causal_delayed_head HandshakeSecurity.StagedConservation.Terminal.deadObserved; exact actual_dead _ _ _)
  | (causal_delayed_head receiptObserved; apply result_receipt)
  | (causal_delayed_completion_head getPeerMixed; exact peer _)
  | (causal_delayed_completion_head getTxSkbPrefix; exact packet _)
  | (causal_delayed_completion_head modifyPeerKeysPrefix; apply modify_peer; intro p timer; rfl)
  | (causal_delayed_completion_head timersAnyAuthenticatedPacketSentPrefix; exact sent _)
  | (causal_delayed_completion_head Completion.send; exact send _ _ _)
  | (causal_delayed_completion_head TxDisposition.drop; exact drop _ _)
  | (causal_delayed_completion_head TxDisposition.dispose; exact dispose _ _ _)
  | (causal_delayed_completion_head emitPrefix; exact emitted _)
  | (causal_delayed_completion_head liftPrefix; apply native)
  | (causal_delayed_native_head PrevQueue.peek
     exact state_framed _ (retained_store (prevQueuePeek_sameWGStore _))
       (DelayedEffects.queue_of_frame (WorkQueueFrames.store (prevQueuePeek_sameWGStore _))))
  | (causal_delayed_head liftWGPrefix; solve | causal_delayed_native)
  | (causal_delayed_head LifetimeEffects.traversalWith; exact product_state (lifetime_traversal _))
  | (causal_delayed_head LifetimeEffects.dataSentWith; exact product_state (lifetime_data_sent _))
  | (causal_delayed_head LifetimeEffects.freshWith; exact product_state (lifetime_actual_fresh _))
  | causal_delayed_product_step)

private theorem complete (pid : PeerId) (item : List SkbId) :
    ProductSafe (CompletionEffects.completeWith observed pid item) := by
  unfold CompletionEffects.completeWith TxDisposition.andObs
  simp only [observed,completionOps,HandshakeSecurity.StagedConservation.SendResult.decorate,HandshakeSecurity.StagedConservation.SendResult.observed,CompletionEffects.observed,CompletionEffects.focused,CompletionEffects.native]
  repeat' causal_delayed_completion_step

private theorem complete_scope (pid : PeerId) (item : List SkbId) : ProductSafe
    (CompletionEffects.completeScoped Event.scope CausalSources.Cause.completion observed pid item) :=
  product_scope (.completion pid item) _ (fun _ => complete pid item)

private theorem body (pid : PeerId) (first : Option (List SkbId)) : ProductSafe
    (HandshakeSecurity.StagedConservation.Terminal.bodyWith observed
      (CompletionEffects.completeScoped Event.scope CausalSources.Cause.completion observed)
      (HandshakeSecurity.StagedConservation.Terminal.deadObserved txEvent txEvent? Event.stagedDisposal Event.terminalDrop) pid first) := by
  unfold HandshakeSecurity.StagedConservation.Terminal.bodyWith TxDisposition.andObs
  simp only [observed,completionOps,HandshakeSecurity.StagedConservation.SendResult.decorate,HandshakeSecurity.StagedConservation.SendResult.observed,CompletionEffects.observed,CompletionEffects.focused,CompletionEffects.native]
  repeat' first
    | (causal_delayed_head CompletionEffects.completeScoped; exact complete_scope _ _)
    | causal_delayed_completion_step

theorem transmit (pid : PeerId) : ProductSafe (CausalJournal.transmit pid) := by
  unfold CausalJournal.transmit HandshakeSecurity.StagedConservation.Terminal.stepWith
  simp only [completionOps,HandshakeSecurity.StagedConservation.SendResult.decorate,HandshakeSecurity.StagedConservation.SendResult.observed,CompletionEffects.observed,CompletionEffects.focused,CompletionEffects.native]
  repeat' first
    | (causal_delayed_head HandshakeSecurity.StagedConservation.Terminal.bodyWith; exact body _ _)
    | causal_delayed_completion_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
