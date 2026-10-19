import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionContracts

/-! Whole completion and ordinary cleanup, conditional on explicit local
callback contracts. The conclusion covers every prefix, including a stopped
post-socket accounting path; no failed-run branch is replaced by True. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity HandshakeSecurity.StagedDisposal CompletionCuts

private theorem and_checked (context : Context) (phase : Phase) (first second : Bool) :
    Holds context phase (TxDisposition.andObs
      (CausalJournal.completionOps.step (branch .doneSendOk first))
      (CausalJournal.completionOps.step (branch .doneNotKeepalive second))) := by
  unfold TxDisposition.andObs Holds
  apply Ensures.bind (branch_state _ _ _ _)
  intro value
  cases value
  · exact Ensures.pure (fun _ _ before => before)
  · exact branch_state _ _ _ _

theorem iteration_checked (callbacks : Callbacks context key) (skb : SkbId)
    (remaining : List SkbId) (dataSent : Bool) :
    Ensures (State context (.sending (skb :: remaining))) (Stopped context)
      (iteration CausalJournal.completionOps context.pid skb dataSent)
      (fun _ => State context (.sending remaining)) := by
  unfold iteration
  apply Ensures.bind (callbacks.packet skb remaining)
  intro packet
  apply Ensures.bind (Q := fun _ h w => State context (.sending (skb :: remaining)) h w ∧ PacketAt skb packet w)
  · intro w history before
    rw [branch_run]
    exact ⟨[],by simp,before.1.sameWG rfl,before.2.sameWG rfl⟩
  intro _
  apply Ensures.bind (callbacks.send skb remaining packet)
  intro sent
  apply Ensures.bind (and_checked context (.sending remaining) sent
    (!(packet.value.bytes.length == MESSAGE_DATA_LEN_0)))
  intro value
  cases value <;> exact Ensures.pure (fun _ _ before => before)

theorem sendLoop_checked (callbacks : Callbacks context key) (remaining : List SkbId)
    (dataSent : Bool) :
    Ensures (State context (.sending remaining)) (Stopped context)
      (sendLoop CausalJournal.completionOps context.pid remaining dataSent)
      (fun _ => State context (.sending [])) := by
  induction remaining generalizing dataSent with
  | nil => exact Ensures.pure (fun _ _ before => before)
  | cons skb remaining ih =>
    unfold sendLoop
    exact Ensures.bind (iteration_checked callbacks skb remaining dataSent) ih

theorem finish_checked (callbacks : Callbacks context key) (dataSent : Bool) :
    Holds context (.sending []) (finish CausalJournal.completionOps context.pid dataSent) := by
  unfold finish Holds
  apply Ensures.bind (branch_state _ _ _ _)
  intro _
  apply Ensures.bind (branch_state _ _ _ _)
  intro sent
  cases sent
  · exact callbacks.fresh
  · exact Ensures.bind callbacks.dataSent (fun _ => callbacks.fresh)

theorem complete_checked (callbacks : Callbacks context key) :
    Ensures (State context (.sending context.items)) (Stopped context)
      (CompletionEffects.completeWith CausalJournal.completionOps context.pid context.items)
      (fun _ => State context (.sending [])) := by
  rw [← complete_factor]
  unfold complete
  exact Ensures.bind callbacks.marker (fun _ =>
    Ensures.bind callbacks.traversal (fun _ =>
      Ensures.bind callbacks.authenticated (fun _ =>
        Ensures.bind (sendLoop_checked callbacks context.items false) (finish_checked callbacks))))

/-- The actual completion scope leaves every processed item terminal and
physically held for cleanup. A stopped inner callback exports its explicit
frontier rather than losing the already-recorded terminal result. -/
theorem completeScoped_checked (callbacks : Callbacks context key) :
    Ensures (State context (.sending context.items)) (Stopped context)
      (CompletionEffects.completeScoped CausalJournal.Event.scope CausalSources.Cause.completion
        CausalJournal.completionOps context.pid context.items)
      (fun _ => State context (.freeing context.items)) := by
  apply (scoped_checked context _ _ _ _ (complete_checked callbacks)).consequence
  · exact fun _ _ before => before
  · exact fun _ _ _ after => after.ready_to_free

theorem freeLoop_checked (callbacks : Callbacks context key) (remaining : List SkbId) :
    Ensures (State context (.freeing remaining)) (Stopped context)
      (freeLoop (TxSource.observed CausalJournal.txEvent CausalJournal.txEvent?
        CausalJournal.Event.stagedDisposal) remaining)
      (fun _ => State context (.freeing [])) := by
  induction remaining with
  | nil => exact Ensures.pure (fun _ _ before => before)
  | cons skb remaining ih =>
    unfold freeLoop
    exact Ensures.bind (callbacks.free skb remaining) (fun _ => ih)

theorem dispose_checked (callbacks : Callbacks context key) :
    Ensures (State context (.freeing context.items)) (Stopped context)
      (CausalJournal.completionOps.dispose context.pid context.items key)
      (fun _ => State context (.freeing [])) := by
  change Ensures _ _ (TxSource.dispose _ _ _ _) _
  rw [← dispose_factor]
  unfold dispose release
  exact Ensures.bind (freeLoop_checked callbacks context.items) (fun _ =>
    Ensures.bind callbacks.keyRelease (fun _ =>
      Ensures.bind callbacks.peerRelease (fun _ =>
        Ensures.pure (fun _ _ before => before))))

def completedAndDisposed (context : Context) (key : KeypairId) : PrefixM CausalJournal.Event Bool := do
  CompletionEffects.completeScoped CausalJournal.Event.scope CausalSources.Cause.completion
    CausalJournal.completionOps context.pid context.items
  CausalJournal.completionOps.dispose context.pid context.items key

/-- This is the exact completed-crypted-batch suffix: scoped native sends,
timer callbacks, individual native frees and both reference repayments.
Normal return has no remaining local cell; failure retains the caller's
concrete last-cut state and first-terminal obligations. -/
theorem completedAndDisposed_checked (callbacks : Callbacks context key) :
    Ensures (State context (.sending context.items)) (Stopped context)
      (completedAndDisposed context key) (fun _ => State context (.freeing [])) :=
  Ensures.bind (completeScoped_checked callbacks) (fun _ => dispose_checked callbacks)

theorem completedAndDisposed_stopped (callbacks : Callbacks context key)
    (before : State context (.sending context.items) history w)
    (run : runPrefix (completedAndDisposed context key) w history = (.error reason,after)) :
    Stopped context reason after :=
  (completedAndDisposed_checked callbacks).failed before run

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
