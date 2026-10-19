import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionCompletionSend
import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionProductSource
import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionLifetime
import Leanux.Proofs.WG.AuthenticatedEffects.EmissionCompletionFrames

/-! Ordered append accounting through the actual final-journal TX completion,
including timer effects, packet disposal and normal/error socket branches.
An endpoint carrier is a local source contract, not global pre-delivery coverage. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do
open TransmitSecurity Queues
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

private abbrev observed := CompletionEffects.observed
  (Event.old ∘ Journal.completionEvent) completion? scope? Event.armed Event.queued

private theorem peer (pid : PeerId) : ProductSafe
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion? (Completion.access (getPeerMixed pid))) :=
  completion_access _ _ (getPeerMixed_erases pid) (by sent_frame [] using [getPeer_sent_spec])

private theorem packet (id : SkbId) : ProductSafe
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion? (Completion.access (getTxSkbPrefix id))) :=
  completion_access _ _ (getTxSkbPrefix_erases id) (EmissionFrames.skb _)

private theorem modify_peer (pid : PeerId) (f : Peer → Peer) : ProductSafe
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion? (Completion.access (modifyPeerKeysPrefix pid f))) :=
  completion_access _ _ (modifyPeerKeysPrefix_erases pid f)
    (by sent_frame [] using [getPeer_sent_spec,setPeer_sent_spec])

private theorem sent (pid : PeerId) : ProductSafe
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion?
      (Completion.access (timersAnyAuthenticatedPacketSentPrefix pid))) :=
  completion_access _ _ (timersAnyAuthenticatedPacketSentPrefix_erases pid) (EmissionFrames.delete pid .sendKeepalive)

private theorem disposition (body : PrefixM TxDisposition.Event α) (native : WG.M α)
    (erases : ErasesPrefix body (liftWG native)) (frame : SameView WGWorld.sent native) : ProductSafe
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion?
      (focusPrefix Completion.Event.disposition Completion.disposition? body)) := by
  apply product_observed _ native (focusPrefix_erases _ _ (focusPrefix_erases _ _ erases))
    (Appends.focus _ _ _)
  · rw [CompletionEffects.focus_composed]
    exact focus_quiet _ _ (fun _ => rfl) _
  · exact frame

private theorem drop (pid : PeerId) (item : List SkbId) : ProductSafe
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion?
      (focusPrefix Completion.Event.disposition Completion.disposition? (TxDisposition.drop pid item))) :=
  disposition _ _ (TxDisposition.drop_erases pid item)
    (by sent_frame [] using [getPeer_sent_spec,setPeer_sent_spec])

private theorem dispose (pid : PeerId) (item : List SkbId) (key : KeypairId) : ProductSafe
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion?
      (focusPrefix Completion.Event.disposition Completion.disposition? (TxDisposition.dispose pid item key))) :=
  disposition _ _ (TxDisposition.dispose_erases pid item key) (EmissionFrames.dispose pid item key)

private theorem native (action : WG.M α) (frame : SameView WGWorld.sent action) : ProductSafe
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion? (liftPrefix (liftWG action))) :=
  (FocusedInvariant.lift _ _ _ (product_wg action (state_native action frame))).2

private theorem emitted_disposition (event : TxDisposition.Event) : ProductSafe
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion? (emitPrefix (.disposition event))) := by
  intro w h hi
  have observed : runPrefix
      (focusPrefix (Event.old ∘ Journal.completionEvent) completion? (emitPrefix (.disposition event))) w h =
      (.ok ((),w),h ++ [Event.old (.disposition event)]) := by
    change (Except.ok (ε := Stop) ((),w),h ++ (((h.filterMap completion? ++ [Completion.Event.disposition event]).drop
      (h.filterMap completion?).length).map (Event.old ∘ Journal.completionEvent))) = _
    simp only [List.drop_append_length,List.map_cons,List.map_nil,Function.comp_apply,Journal.completionEvent]
  rw [observed]
  exact ⟨[Event.old (.disposition event)],rfl,True.intro,hi.quiet _ rfl⟩

open Lean Meta Elab Tactic in
elab "emission_completion_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``ProductSafe do throwError "not an emission product contract"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  unless action.isAppOf ``focusPrefix do throwError "not a focused completion callback"
  let body := action.getAppArgs.back!.consumeMData.headBeta
  let body := if body.isAppOf ``Completion.access || body.isAppOf ``focusPrefix then
      body.getAppArgs.back!.consumeMData.headBeta else body
  let .const actual _ := body.getAppFn | throwError "not a constant callback"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do throwError "different callback"

macro "emission_completion_step" : tactic => `(tactic| first
  | (emission_completion_head getPeerMixed; exact peer _)
  | (emission_completion_head getTxSkbPrefix; exact packet _)
  | (emission_completion_head modifyPeerKeysPrefix; exact modify_peer _ _)
  | (emission_completion_head timersAnyAuthenticatedPacketSentPrefix; exact sent _)
  | (emission_completion_head Completion.send; exact completion_send _ _ _)
  | (emission_completion_head TxDisposition.drop; exact drop _ _)
  | (emission_completion_head TxDisposition.dispose; exact dispose _ _ _)
  | (emission_completion_head emitPrefix; exact emitted_disposition _)
  | (emission_completion_head liftPrefix; apply native)
  | (emission_frame_head PrevQueue.peek; exact EmissionFrames.peek _)
  | (emission_frame_head branch; sent_frame [] using [])
  | (emission_frame_head invariant; sent_frame [] using [])
  | (emission_head liftWGObserver; apply product_state)
  | (emission_head LifetimeEffects.traversalWith; exact lifetime_traversal _)
  | (emission_head LifetimeEffects.dataSentWith; exact lifetime_data_sent _)
  | (emission_head LifetimeEffects.freshWith; exact lifetime_fresh _)
  | emission_product_step)

private theorem complete (pid : PeerId) (item : List SkbId) :
    ProductSafe (CompletionEffects.completeWith observed pid item) := by
  unfold CompletionEffects.completeWith TxDisposition.andObs
  simp only [observed,CompletionEffects.observed,CompletionEffects.focused,CompletionEffects.native]
  repeat' emission_completion_step

private theorem complete_scope (pid : PeerId) (item : List SkbId) : ProductSafe
    (CompletionEffects.completeScoped Event.scope CausalSources.Cause.completion observed pid item) :=
  product_scope (.completion pid item) _ (fun _ => complete pid item)

private theorem body (pid : PeerId) (first : Option (List SkbId)) : ProductSafe
    (CompletionEffects.bodySourceWith observed
      (CompletionEffects.completeScoped Event.scope CausalSources.Cause.completion observed) pid first) := by
  unfold CompletionEffects.bodySourceWith TxDisposition.andObs
  simp only [observed,CompletionEffects.observed,CompletionEffects.focused,CompletionEffects.native]
  repeat' first
    | (emission_head CompletionEffects.completeScoped; exact complete_scope _ _)
    | emission_completion_step

theorem transmit (pid : PeerId) : ProductSafe (CausalJournal.transmit pid) := by
  unfold CausalJournal.transmit CompletionEffects.observedStep CompletionEffects.stepScoped CompletionEffects.stepSourceWith
  simp only [CompletionEffects.observed,CompletionEffects.focused,CompletionEffects.native]
  repeat' first
    | (emission_head CompletionEffects.bodySourceWith; exact body _ _)
    | emission_completion_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
