import Leanux.Proofs.WG.AuthenticatedEffects.CausalJournalOldProjection
import Leanux.Proofs.WG.AuthenticatedEffects.CausalEffectsFrames

/-! Independent history frames exclude exchange receipts from the actual TX
completion source. Native erasure alone would not establish this exclusion. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ExchangeCausal
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity AuthenticatedEffects
open CausalJournal
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

private theorem lifetime_focus (a : MixedM α) :
    StateHistoryFrame exchange?
      (focusStatePrefix (Event.old ∘ Journal.completionEvent ∘ CompletionEffects.lifetimeEvent)
        (fun e => (completion? e).bind CompletionEffects.lifetime?) a) :=
  fun w => focusPrefix_other _ _ exchange? (fun _ => rfl) (a.run w)

private theorem lifted_history (a : WGPrefix Event α) (h : StateHistoryFrame exchange? a) :
    HistoryFrame exchange? (liftWGObserver a) := fun w hist => h w.wg w.ambient hist

private theorem effect_arm (pid : PeerId) (timer : PeerTimer) (delay : Nat) (caller : Option UInt64) :
    StateHistoryFrame exchange?
      ((LifetimeEffects.decorate
        (CompletionEffects.lifetimeBase (Event.old ∘ Journal.completionEvent) completion?)
        scope? Event.armed Event.queued).arm pid timer delay caller) :=
  CausalEffects.atCurrent_frame scope? _ exchange?
    (fun _ => StateHistoryFrame.receiptWGObserved (lifetime_focus _) _ (fun _ => rfl))

private theorem effect_append (pid : PeerId) :
    StateHistoryFrame exchange?
      ((LifetimeEffects.decorate
        (CompletionEffects.lifetimeBase (Event.old ∘ Journal.completionEvent) completion?)
        scope? Event.armed Event.queued).append pid) :=
  CausalEffects.atCurrent_frame scope? _ exchange?
    (fun _ => StateHistoryFrame.receiptWGObserved (lifetime_focus _) _ (fun _ => rfl))

private def lifetimeOps := LifetimeEffects.decorate
  (CompletionEffects.lifetimeBase (Event.old ∘ Journal.completionEvent) completion?)
  scope? Event.armed Event.queued

open Lean Meta Elab Tactic in
elab "exchange_frame_head " name:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  let args := target.getAppArgs
  unless args.size > 0 do throwError "not a frame"
  let action := args.back!.consumeMData
  let .const actual _ := action.getAppFn | throwError "not a constant action"
  let expected := name.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    throwError "different action"

macro "exchange_lifetime_frame" : tactic => `(tactic| first
  | (exchange_frame_head LifetimeEffects.Ops.arm; exact effect_arm _ _ _ _)
  | (exchange_frame_head LifetimeEffects.Ops.append; exact effect_append _)
  | (exchange_frame_head LifetimeEffects.Ops.step; exact lifetime_focus _)
  | (exchange_frame_head LifetimeEffects.Ops.peer; exact lifetime_focus _)
  | (exchange_frame_head LifetimeEffects.Ops.keypair; exact lifetime_focus _)
  | (exchange_frame_head LifetimeEffects.Ops.modifyPeer; exact lifetime_focus _)
  | (exchange_frame_head LifetimeEffects.Ops.guard; exact lifetime_focus _)
  | (exchange_frame_head LifetimeEffects.Ops.get; exact lifetime_focus _)
  | (exchange_frame_head LifetimeEffects.Ops.put; exact lifetime_focus _)
  | (exchange_frame_head Pure.pure; exact fun _ _ _ => rfl)
  | (exchange_frame_head Bind.bind; apply StateHistoryFrame.bind)
  | (maintenance_intro; try dsimp only)
  | dsimp (config := {failIfUnchanged := true}) only
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

private theorem modify_history (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    StateHistoryFrame exchange? (LifetimeEffects.modifyWith lifetimeOps site pid timer delay) := by
  unfold LifetimeEffects.modifyWith
  repeat' exchange_lifetime_frame

private theorem traversal_history (pid : PeerId) :
    StateHistoryFrame exchange? (LifetimeEffects.traversalWith lifetimeOps pid) := by
  unfold LifetimeEffects.traversalWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (exchange_frame_head LifetimeEffects.modifyWith; exact modify_history _ _ _ _)
    | exchange_lifetime_frame

private theorem data_history (pid : PeerId) :
    StateHistoryFrame exchange? (LifetimeEffects.dataSentWith lifetimeOps pid) := by
  unfold LifetimeEffects.dataSentWith
  repeat' exchange_lifetime_frame

private theorem queue_history (pid : PeerId) (retry : Bool) :
    StateHistoryFrame exchange? (LifetimeEffects.queuedWith lifetimeOps pid retry) := by
  unfold LifetimeEffects.queuedWith
  repeat' exchange_lifetime_frame

private theorem fresh_history (pid : PeerId) :
    StateHistoryFrame exchange? (LifetimeEffects.freshWith lifetimeOps pid) := by
  unfold LifetimeEffects.freshWith
  simp only [andPrefix,orPrefix]
  repeat' first
    | (exchange_frame_head LifetimeEffects.queuedWith; exact queue_history _ _)
    | exchange_lifetime_frame

private def completionOps := CompletionEffects.observed
  (Event.old ∘ Journal.completionEvent) completion? scope? Event.armed Event.queued

private theorem capture_history (g : PrefixM Event α) (h : HistoryFrame exchange? g) :
    HistoryFrame exchange? (captureObserved g) := by
  intro w hist
  rw [runPrefix_captureObserved]
  cases run : runPrefix g w hist with
  | mk result history => cases result <;> simpa only [run] using h w hist

private theorem old_history (g : PrefixM Completion.Event α) :
    HistoryFrame exchange?
      (focusPrefix (Event.old ∘ Journal.completionEvent) completion? g) :=
  focusPrefix_other _ _ exchange? (fun _ => rfl) g

macro "exchange_completion_frame" : tactic => `(tactic| first
  | (exchange_frame_head CompletionEffects.Ops.traversal; exact lifted_history _ (traversal_history _))
  | (exchange_frame_head CompletionEffects.Ops.dataSent; exact lifted_history _ (data_history _))
  | (exchange_frame_head CompletionEffects.Ops.fresh; exact lifted_history _ (fresh_history _))
  | (exchange_frame_head CompletionEffects.Ops.step; exact old_history _)
  | (exchange_frame_head CompletionEffects.Ops.peer; exact old_history _)
  | (exchange_frame_head CompletionEffects.Ops.modifyPeer; exact old_history _)
  | (exchange_frame_head CompletionEffects.Ops.packet; exact old_history _)
  | (exchange_frame_head CompletionEffects.Ops.completion; exact old_history _)
  | (exchange_frame_head CompletionEffects.Ops.send; exact old_history _)
  | (exchange_frame_head CompletionEffects.Ops.drop; exact old_history _)
  | (exchange_frame_head CompletionEffects.Ops.dispose; exact old_history _)
  | (exchange_frame_head CompletionEffects.Ops.sent; exact old_history _)
  | (exchange_frame_head captureObserved; apply capture_history)
  | (exchange_frame_head Pure.pure; exact HistoryFrame.pure exchange? _)
  | (exchange_frame_head Bind.bind; apply HistoryFrame.bind)
  | (exchange_frame_head ForIn.forIn; apply HistoryFrame.forIn)
  | (maintenance_intro; try dsimp only)
  | dsimp (config := {failIfUnchanged := true}) only
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

private theorem complete_history (pid : PeerId) (item : List SkbId) :
    HistoryFrame exchange? (CompletionEffects.completeWith completionOps pid item) := by
  unfold CompletionEffects.completeWith TxDisposition.andObs
  repeat' exchange_completion_frame

private theorem scope_history (cause : Cause) (g : PrefixM Event α)
    (h : HistoryFrame exchange? g) :
    HistoryFrame exchange? (CausalScope.prefixScope Event.scope cause (fun _ => g)) := by
  intro w hist
  rw [CausalScope.prefix_run]
  have old := h w (hist ++ [Event.scope (.entered ⟨hist.length,cause⟩)])
  cases run : runPrefix g w (hist ++ [Event.scope (.entered ⟨hist.length,cause⟩)]) with
  | mk result history =>
    rw [run] at old
    cases result <;> simpa only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,
      exchange?,List.append_nil] using old

private theorem body_history (pid : PeerId) (first : Option (List SkbId)) :
    HistoryFrame exchange? (CompletionEffects.bodySourceWith completionOps
      (CompletionEffects.completeScoped Event.scope CausalSources.Cause.completion completionOps) pid first) := by
  unfold CompletionEffects.bodySourceWith TxDisposition.andObs
  repeat' first
    | (exchange_frame_head CompletionEffects.completeScoped; exact scope_history _ _ (complete_history _ _))
    | exchange_completion_frame

theorem transmit_history (pid : PeerId) : HistoryFrame exchange? (transmit pid) := by
  change HistoryFrame exchange? (CompletionEffects.stepSourceWith completionOps
    (CompletionEffects.completeScoped Event.scope CausalSources.Cause.completion completionOps) pid)
  unfold CompletionEffects.stepSourceWith
  repeat' first
    | (exchange_frame_head CompletionEffects.bodySourceWith; exact body_history _ _)
    | exchange_completion_frame

end Leanux.Proofs.WG.HandshakeSecurity.ExchangeCausal
