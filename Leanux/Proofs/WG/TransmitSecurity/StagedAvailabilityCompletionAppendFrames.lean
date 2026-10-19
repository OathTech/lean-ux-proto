import Leanux.Proofs.WG.AuthenticatedEffects.CausalCallbackQuietActors
import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptLifetime

/-! Append-only histories of the actual TX completion source. This structural
fact retains the first Stop and requires no incoming receipt-validity invariant. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.CallbackQuiet
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity Lifetimes Queues
open HandshakeSecurity.StagedDisposal HandshakeSecurity.StagedConservation
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

private theorem state_true (h : StateAppends body) : Driver.StateHistorySafe (fun _ => True) body := by
  intro w a events _
  obtain ⟨suffix,grown⟩ := h w a events
  refine ⟨suffix,grown,True.intro,?_⟩
  cases (runPrefix (body.run w) a events).1 <;> trivial

private theorem product_true (h : Appends body) : Driver.ProductHistorySafe (fun _ => True) body := by
  intro w events _
  obtain ⟨suffix,grown⟩ := h w events
  refine ⟨suffix,grown,True.intro,?_⟩
  cases (runPrefix body w events).1 <;> trivial

private theorem state_appends (h : Driver.StateHistorySafe (fun _ => True) body) : StateAppends body := by
  intro w a events
  obtain ⟨suffix,grown,_,_⟩ := h w a events True.intro
  exact ⟨suffix,grown⟩

private theorem product_appends (h : Driver.ProductHistorySafe (fun _ => True) body) : Appends body := by
  intro w events
  obtain ⟨suffix,grown,_,_⟩ := h w events True.intro
  exact ⟨suffix,grown⟩

private abbrev emptyProjection : Event → Option Unit := fun _ => none

private theorem lifetime_appends : LifetimeEffects.Ops.Appends completionLifetime where
  step := fun _ => StateAppends.focus _ _ _
  peer := fun _ => StateAppends.focus _ _ _
  keypair := fun _ => StateAppends.focus _ _ _
  modifyPeer := fun _ _ => StateAppends.focus _ _ _
  guard := fun _ => StateAppends.focus _ _ _
  get := fun _ => StateAppends.focus _ _ _
  put := fun peer => (CallbackQuiet.peer emptyProjection _ _ (fun _ => rfl) (fun _ => rfl) peer).1
  arm := fun pid timer delay caller w a h =>
    ((StateAppends.focus _ _ _).receiptWGObserved
      (fun r => Event.armed ⟨CausalScope.current scope? h,pid,timer,delay,caller,r⟩)) w a h
  append := fun pid w a h =>
    ((StateAppends.focus _ _ _).receiptWGObserved
      (fun r => Event.queued ⟨CausalScope.current scope? h,pid,r⟩)) w a h

private theorem legacy_lifetime_appends : LifetimeEffects.Ops.Appends Receipts.lifetime where
  step := fun _ => StateAppends.focus _ _ _
  peer := fun _ => StateAppends.focus _ _ _
  keypair := fun _ => StateAppends.focus _ _ _
  modifyPeer := fun _ _ => StateAppends.focus _ _ _
  guard := fun _ => StateAppends.focus _ _ _
  get := fun _ => StateAppends.focus _ _ _
  put := fun _ => StateAppends.focus _ _ _
  arm := fun pid timer delay caller w a h =>
    ((StateAppends.focus _ _ _).receiptWGObserved
      (fun r => Event.armed ⟨CausalScope.current scope? h,pid,timer,delay,caller,r⟩)) w a h
  append := fun pid w a h =>
    ((StateAppends.focus _ _ _).receiptWGObserved
      (fun r => Event.queued ⟨CausalScope.current scope? h,pid,r⟩)) w a h

macro "available_append_lifetime " h:ident : tactic => `(tactic| first
  | (driver_history_head LifetimeEffects.Ops.step; exact state_true (($h).step _))
  | (driver_history_head LifetimeEffects.Ops.peer; exact state_true (($h).peer _))
  | (driver_history_head LifetimeEffects.Ops.keypair; exact state_true (($h).keypair _))
  | (driver_history_head LifetimeEffects.Ops.modifyPeer; exact state_true (($h).modifyPeer _ _))
  | (driver_history_head LifetimeEffects.Ops.guard; exact state_true (($h).guard _))
  | (driver_history_head LifetimeEffects.Ops.arm; exact state_true (($h).arm _ _ _ _))
  | (driver_history_head LifetimeEffects.Ops.get; exact state_true (($h).get _))
  | (driver_history_head LifetimeEffects.Ops.put; exact state_true (($h).put _))
  | (driver_history_head LifetimeEffects.Ops.append; exact state_true (($h).append _))
  | driver_state_history_step)

private theorem lifetime_modify {o : LifetimeEffects.Ops (WGPrefix Event)}
    (h : LifetimeEffects.Ops.Appends o) (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    Driver.StateHistorySafe (fun _ => True) (LifetimeEffects.modifyWith o site pid timer delay) := by
  unfold LifetimeEffects.modifyWith
  repeat' available_append_lifetime h

private theorem lifetime_traversal_append (pid : PeerId) :
    StateAppends (LifetimeEffects.traversalWith Receipts.lifetime pid) := by
  apply state_appends
  unfold LifetimeEffects.traversalWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (driver_history_head LifetimeEffects.modifyWith; exact lifetime_modify legacy_lifetime_appends _ _ _ _)
    | available_append_lifetime legacy_lifetime_appends

private theorem lifetime_data_append (pid : PeerId) :
    StateAppends (LifetimeEffects.dataSentWith Receipts.lifetime pid) := by
  apply state_appends
  unfold LifetimeEffects.dataSentWith
  repeat' available_append_lifetime legacy_lifetime_appends

private theorem lifetime_queued_append (pid : PeerId) (retry : Bool) :
    Driver.StateHistorySafe (fun _ => True) (LifetimeEffects.queuedWith completionLifetime pid retry) := by
  unfold LifetimeEffects.queuedWith
  repeat' available_append_lifetime lifetime_appends

private theorem lifetime_fresh_append (pid : PeerId) :
    StateAppends (LifetimeEffects.freshWith completionLifetime pid) := by
  apply state_appends
  unfold LifetimeEffects.freshWith andPrefix orPrefix
  repeat' first
    | (driver_history_head LifetimeEffects.queuedWith; exact lifetime_queued_append _ _)
    | available_append_lifetime lifetime_appends

private theorem actual_dispose (pid : PeerId) (item : List SkbId) (key : KeypairId) :
    Driver.ProductHistorySafe (fun _ => True) (completionOps.dispose pid item key) :=
  product_true (CallbackQuiet.dispose emptyProjection (fun _ => rfl) (fun _ => rfl) pid item key).1

private theorem actual_dead (pid : PeerId) (item : List SkbId) (head : DataPacket) :
    Driver.ProductHistorySafe (fun _ => True)
      (Terminal.deadObserved txEvent txEvent? Event.stagedDisposal Event.terminalDrop pid item head) :=
  product_true (CallbackQuiet.dead emptyProjection (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) pid item head).1

macro "available_append_completion" : tactic => `(tactic| first
  | (driver_history_head TxSource.dispose; exact actual_dispose _ _ _)
  | (driver_history_head Terminal.deadObserved; exact actual_dead _ _ _)
  | (driver_history_head captureObserved; exact product_true (Appends.captureObserved (Appends.focus _ _ _)))
  | (driver_history_head receiptObserved; refine CallbackHistory.product_receipt _ ?_ _
      (fun r => product_true (fun _ _ => ⟨[_],rfl⟩)))
  | (driver_history_head focusPrefix; exact product_true (Appends.focus _ _ _))
  | (driver_history_head LifetimeEffects.traversalWith; exact Driver.History.product_state (state_true (lifetime_traversal_append _)))
  | (driver_history_head LifetimeEffects.dataSentWith; exact Driver.History.product_state (state_true (lifetime_data_append _)))
  | (driver_history_head LifetimeEffects.freshWith; exact Driver.History.product_state (state_true (lifetime_fresh_append _)))
  | driver_product_history_step)

private theorem complete_append (pid : PeerId) (item : List SkbId) :
    Appends (CompletionEffects.completeWith completionOps pid item) := by
  apply product_appends
  unfold CompletionEffects.completeWith TxDisposition.andObs
  simp only [completionOps,SendResult.decorate,SendResult.observed,CompletionEffects.observed,CompletionEffects.focused]
  repeat' available_append_completion

private theorem complete_scope_append (pid : PeerId) (item : List SkbId) :
    Appends (CompletionEffects.completeScoped Event.scope CausalSources.Cause.completion completionOps pid item) := by
  intro w h
  obtain ⟨suffix,grown⟩ := CausalScope.prefix_entry Event.scope (.completion pid item)
    (fun _ => CompletionEffects.completeWith completionOps pid item) (fun _ => complete_append pid item) w h
  exact ⟨_ :: suffix,grown⟩

private theorem body_append (pid : PeerId) (first : Option (List SkbId)) :
    Driver.ProductHistorySafe (fun _ => True) (Terminal.bodyWith completionOps
      (CompletionEffects.completeScoped Event.scope CausalSources.Cause.completion completionOps)
      (Terminal.deadObserved txEvent txEvent? Event.stagedDisposal Event.terminalDrop) pid first) := by
  unfold Terminal.bodyWith TxDisposition.andObs
  simp only [completionOps,SendResult.decorate,SendResult.observed,CompletionEffects.observed,CompletionEffects.focused]
  repeat' first
    | (driver_history_head CompletionEffects.completeScoped; exact product_true (complete_scope_append _ _))
    | available_append_completion

/-- Every actual completion extends its incoming history even if a later
socket, reference repayment or terminal cleanup stops. -/
theorem transmit_appends (pid : PeerId) : Appends (CausalJournal.transmit pid) := by
  apply product_appends
  unfold CausalJournal.transmit Terminal.stepWith
  simp only [completionOps,SendResult.decorate,SendResult.observed,CompletionEffects.observed,CompletionEffects.focused]
  repeat' first
    | (driver_history_head Terminal.bodyWith; exact body_append _ _)
    | available_append_completion

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.CallbackQuiet
