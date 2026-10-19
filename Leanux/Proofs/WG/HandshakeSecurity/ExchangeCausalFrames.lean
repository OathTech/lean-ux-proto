import Leanux.Proofs.WG.AuthenticatedEffects.CausalJournalOldProjection
import Leanux.Proofs.WG.AuthenticatedEffects.CausalEffectsFrames

/-! Independent history frames exclude exchange receipts from the actual TX
completion source. Native erasure alone would not establish this exclusion. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ExchangeCausal
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity AuthenticatedEffects
open CausalJournal
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

private theorem lifetime_focus (rho : Event → Option F)
    (oldQuiet : ∀ e, rho (Event.old (Journal.completionEvent e)) = none) (a : MixedM α) :
    StateHistoryFrame rho
      (focusStatePrefix (Event.old ∘ Journal.completionEvent ∘ CompletionEffects.lifetimeEvent)
        (fun e => (completion? e).bind CompletionEffects.lifetime?) a) :=
  fun w => focusPrefix_other _ _ rho (fun e => oldQuiet (CompletionEffects.lifetimeEvent e)) (a.run w)

private theorem lifted_history (rho : Event → Option F) (a : WGPrefix Event α) (h : StateHistoryFrame rho a) :
    HistoryFrame rho (liftWGObserver a) := fun w hist => h w.wg w.ambient hist

private theorem effect_arm (rho : Event → Option F)
    (oldQuiet : ∀ e, rho (Event.old (Journal.completionEvent e)) = none)
    (armQuiet : ∀ e, rho (Event.armed e) = none) (pid : PeerId) (timer : PeerTimer) (delay : Nat) (caller : Option UInt64) :
    StateHistoryFrame rho
      ((LifetimeEffects.decorate
        (CompletionEffects.lifetimeBase (Event.old ∘ Journal.completionEvent) completion?)
        scope? Event.armed Event.queued).arm pid timer delay caller) :=
  CausalEffects.atCurrent_frame scope? _ rho
    (fun _ => StateHistoryFrame.receiptWGObserved (lifetime_focus rho oldQuiet _) _ (fun _ => armQuiet _))

private theorem effect_append (rho : Event → Option F)
    (oldQuiet : ∀ e, rho (Event.old (Journal.completionEvent e)) = none)
    (queueQuiet : ∀ e, rho (Event.queued e) = none) (pid : PeerId) :
    StateHistoryFrame rho
      ((LifetimeEffects.decorate
        (CompletionEffects.lifetimeBase (Event.old ∘ Journal.completionEvent) completion?)
        scope? Event.armed Event.queued).append pid) :=
  CausalEffects.atCurrent_frame scope? _ rho
    (fun _ => StateHistoryFrame.receiptWGObserved (lifetime_focus rho oldQuiet _) _ (fun _ => queueQuiet _))

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

macro "exchange_lifetime_frame " rho:ident oldQuiet:ident armQuiet:ident queueQuiet:ident : tactic => `(tactic| first
  | (exchange_frame_head LifetimeEffects.Ops.arm; exact effect_arm $rho $oldQuiet $armQuiet _ _ _ _)
  | (exchange_frame_head LifetimeEffects.Ops.append; exact effect_append $rho $oldQuiet $queueQuiet _)
  | (exchange_frame_head LifetimeEffects.Ops.step; exact lifetime_focus $rho $oldQuiet _)
  | (exchange_frame_head LifetimeEffects.Ops.peer; exact lifetime_focus $rho $oldQuiet _)
  | (exchange_frame_head LifetimeEffects.Ops.keypair; exact lifetime_focus $rho $oldQuiet _)
  | (exchange_frame_head LifetimeEffects.Ops.modifyPeer; exact lifetime_focus $rho $oldQuiet _)
  | (exchange_frame_head LifetimeEffects.Ops.guard; exact lifetime_focus $rho $oldQuiet _)
  | (exchange_frame_head LifetimeEffects.Ops.get; exact lifetime_focus $rho $oldQuiet _)
  | (exchange_frame_head LifetimeEffects.Ops.put; exact lifetime_focus $rho $oldQuiet _)
  | (exchange_frame_head Pure.pure; exact fun _ _ _ => rfl)
  | (exchange_frame_head Bind.bind; apply StateHistoryFrame.bind)
  | (maintenance_intro; try dsimp only)
  | dsimp (config := {failIfUnchanged := true}) only
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

private theorem modify_history (rho : Event → Option F)
    (oldQuiet : ∀ e, rho (Event.old (Journal.completionEvent e)) = none)
    (armQuiet : ∀ e, rho (Event.armed e) = none) (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    StateHistoryFrame rho (LifetimeEffects.modifyWith lifetimeOps site pid timer delay) := by
  unfold LifetimeEffects.modifyWith
  repeat' exchange_lifetime_frame rho oldQuiet armQuiet queueQuiet

private theorem traversal_history (rho : Event → Option F)
    (oldQuiet : ∀ e, rho (Event.old (Journal.completionEvent e)) = none)
    (armQuiet : ∀ e, rho (Event.armed e) = none) (pid : PeerId) :
    StateHistoryFrame rho (LifetimeEffects.traversalWith lifetimeOps pid) := by
  unfold LifetimeEffects.traversalWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (exchange_frame_head LifetimeEffects.modifyWith; exact modify_history rho oldQuiet armQuiet _ _ _ _)
    | exchange_lifetime_frame rho oldQuiet armQuiet queueQuiet

private theorem data_history (rho : Event → Option F)
    (oldQuiet : ∀ e, rho (Event.old (Journal.completionEvent e)) = none)
    (armQuiet : ∀ e, rho (Event.armed e) = none) (pid : PeerId) :
    StateHistoryFrame rho (LifetimeEffects.dataSentWith lifetimeOps pid) := by
  unfold LifetimeEffects.dataSentWith
  repeat' exchange_lifetime_frame rho oldQuiet armQuiet queueQuiet

private theorem queue_history (rho : Event → Option F)
    (oldQuiet : ∀ e, rho (Event.old (Journal.completionEvent e)) = none)
    (queueQuiet : ∀ e, rho (Event.queued e) = none) (pid : PeerId) (retry : Bool) :
    StateHistoryFrame rho (LifetimeEffects.queuedWith lifetimeOps pid retry) := by
  unfold LifetimeEffects.queuedWith
  repeat' exchange_lifetime_frame rho oldQuiet armQuiet queueQuiet

private theorem fresh_history (rho : Event → Option F)
    (oldQuiet : ∀ e, rho (Event.old (Journal.completionEvent e)) = none)
    (queueQuiet : ∀ e, rho (Event.queued e) = none) (pid : PeerId) :
    StateHistoryFrame rho (LifetimeEffects.freshWith lifetimeOps pid) := by
  unfold LifetimeEffects.freshWith
  simp only [andPrefix,orPrefix]
  repeat' first
    | (exchange_frame_head LifetimeEffects.queuedWith; exact queue_history rho oldQuiet queueQuiet _ _)
    | exchange_lifetime_frame rho oldQuiet armQuiet queueQuiet

private def completionOps := CompletionEffects.observed
  (Event.old ∘ Journal.completionEvent) completion? scope? Event.armed Event.queued

private theorem capture_history (rho : Event → Option F) (g : PrefixM Event α) (h : HistoryFrame rho g) :
    HistoryFrame rho (captureObserved g) := by
  intro w hist
  rw [runPrefix_captureObserved]
  cases run : runPrefix g w hist with
  | mk result history => cases result <;> simpa only [run] using h w hist

private theorem old_history (rho : Event → Option F)
    (oldQuiet : ∀ e, rho (Event.old (Journal.completionEvent e)) = none) (g : PrefixM Completion.Event α) :
    HistoryFrame rho
      (focusPrefix (Event.old ∘ Journal.completionEvent) completion? g) :=
  focusPrefix_other _ _ rho oldQuiet g

macro "exchange_completion_frame " rho:ident oldQuiet:ident armQuiet:ident queueQuiet:ident : tactic => `(tactic| first
  | (exchange_frame_head CompletionEffects.Ops.traversal; exact lifted_history $rho _ (traversal_history $rho $oldQuiet $armQuiet _))
  | (exchange_frame_head CompletionEffects.Ops.dataSent; exact lifted_history $rho _ (data_history $rho $oldQuiet $armQuiet _))
  | (exchange_frame_head CompletionEffects.Ops.fresh; exact lifted_history $rho _ (fresh_history $rho $oldQuiet $queueQuiet _))
  | (exchange_frame_head CompletionEffects.Ops.step; exact old_history $rho $oldQuiet _)
  | (exchange_frame_head CompletionEffects.Ops.peer; exact old_history $rho $oldQuiet _)
  | (exchange_frame_head CompletionEffects.Ops.modifyPeer; exact old_history $rho $oldQuiet _)
  | (exchange_frame_head CompletionEffects.Ops.packet; exact old_history $rho $oldQuiet _)
  | (exchange_frame_head CompletionEffects.Ops.completion; exact old_history $rho $oldQuiet _)
  | (exchange_frame_head CompletionEffects.Ops.send; exact old_history $rho $oldQuiet _)
  | (exchange_frame_head CompletionEffects.Ops.drop; exact old_history $rho $oldQuiet _)
  | (exchange_frame_head CompletionEffects.Ops.dispose; exact old_history $rho $oldQuiet _)
  | (exchange_frame_head CompletionEffects.Ops.sent; exact old_history $rho $oldQuiet _)
  | (exchange_frame_head captureObserved; apply capture_history $rho)
  | (exchange_frame_head Pure.pure; exact HistoryFrame.pure $rho _)
  | (exchange_frame_head Bind.bind; apply HistoryFrame.bind)
  | (exchange_frame_head ForIn.forIn; apply HistoryFrame.forIn)
  | (maintenance_intro; try dsimp only)
  | dsimp (config := {failIfUnchanged := true}) only
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

private theorem complete_history (rho : Event → Option F)
    (oldQuiet : ∀ e, rho (Event.old (Journal.completionEvent e)) = none)
    (armQuiet : ∀ e, rho (Event.armed e) = none)
    (queueQuiet : ∀ e, rho (Event.queued e) = none) (pid : PeerId) (item : List SkbId) :
    HistoryFrame rho (CompletionEffects.completeWith completionOps pid item) := by
  unfold CompletionEffects.completeWith TxDisposition.andObs
  repeat' exchange_completion_frame rho oldQuiet armQuiet queueQuiet

private theorem scope_history (rho : Event → Option F)
    (scopeQuiet : ∀ e, rho (Event.scope e) = none) (cause : Cause) (g : PrefixM Event α)
    (h : HistoryFrame rho g) :
    HistoryFrame rho (CausalScope.prefixScope Event.scope cause (fun _ => g)) := by
  intro w hist
  rw [CausalScope.prefix_run]
  have old := h w (hist ++ [Event.scope (.entered ⟨hist.length,cause⟩)])
  cases run : runPrefix g w (hist ++ [Event.scope (.entered ⟨hist.length,cause⟩)]) with
  | mk result history =>
    rw [run] at old
    cases result <;> simpa only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,
      scopeQuiet,List.append_nil] using old

private theorem body_history (rho : Event → Option F)
    (oldQuiet : ∀ e, rho (Event.old (Journal.completionEvent e)) = none)
    (armQuiet : ∀ e, rho (Event.armed e) = none)
    (queueQuiet : ∀ e, rho (Event.queued e) = none)
    (scopeQuiet : ∀ e, rho (Event.scope e) = none) (pid : PeerId) (first : Option (List SkbId)) :
    HistoryFrame rho (CompletionEffects.bodySourceWith completionOps
      (CompletionEffects.completeScoped Event.scope CausalSources.Cause.completion completionOps) pid first) := by
  unfold CompletionEffects.bodySourceWith TxDisposition.andObs
  repeat' first
    | (exchange_frame_head CompletionEffects.completeScoped; exact scope_history rho scopeQuiet _ _ (complete_history rho oldQuiet armQuiet queueQuiet _ _))
    | exchange_completion_frame rho oldQuiet armQuiet queueQuiet

theorem transmit_history_of_quiet (rho : Event → Option F)
    (oldQuiet : ∀ e, rho (Event.old (Journal.completionEvent e)) = none)
    (armQuiet : ∀ e, rho (Event.armed e) = none)
    (queueQuiet : ∀ e, rho (Event.queued e) = none)
    (scopeQuiet : ∀ e, rho (Event.scope e) = none) (pid : PeerId) : HistoryFrame rho (transmit pid) := by
  change HistoryFrame rho (CompletionEffects.stepSourceWith completionOps
    (CompletionEffects.completeScoped Event.scope CausalSources.Cause.completion completionOps) pid)
  unfold CompletionEffects.stepSourceWith
  repeat' first
    | (exchange_frame_head CompletionEffects.bodySourceWith; exact body_history rho oldQuiet armQuiet queueQuiet scopeQuiet _ _)
    | exchange_completion_frame rho oldQuiet armQuiet queueQuiet

theorem transmit_history (pid : PeerId) : HistoryFrame exchange? (transmit pid) :=
  transmit_history_of_quiet exchange? (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) pid

end Leanux.Proofs.WG.HandshakeSecurity.ExchangeCausal
