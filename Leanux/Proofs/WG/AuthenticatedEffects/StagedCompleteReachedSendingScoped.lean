import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSendingLoop
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteSequence

/-! The actual completion prelude and scope entry lead to the send loop.
A stopped loop exposes its failed iteration through a fixed prefix of this
same scoped source. Early prelude and later finish failures remain separate. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Sending
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch Staged.Obligations StagedTerminalComplete
variable {initial : Ledger}

def prelude (context : Context) : PrefixM CausalJournal.Event Unit := do
  CausalJournal.completionOps.completion context.pid context.items
  CausalJournal.completionOps.traversal context.pid
  CausalJournal.completionOps.sent context.pid

def entered (context : Context) (history : List CausalJournal.Event) : CausalJournal.Event :=
  .scope (.entered ⟨history.length,CausalSources.Cause.completion context.pid context.items⟩)

def scopedIterationPrefix (context : Context) (done : List SkbId) : PrefixM CausalJournal.Event Bool :=
  fun w => ExceptT.mk fun history => runPrefix (do
    emitPrefix (entered context history)
    prelude context
    sendLoop CausalJournal.completionOps context.pid done false) w history

theorem complete_prelude_factor (context : Context) :
    CompletionEffects.completeWith CausalJournal.completionOps context.pid context.items =
      (prelude context >>= fun _ => do
        let sent ← sendLoop CausalJournal.completionOps context.pid context.items false
        finish CausalJournal.completionOps context.pid sent) := by
  rw [← complete_factor]
  simp only [complete,prelude,bind_assoc]

theorem prelude_checked (context : Context) (initial : Ledger) (original : List CleanupDebt) :
    CompletionCuts.Ensures (Converse.Sending context initial original context.items)
      (Converse.SendingStopped context initial original) (prelude context)
      (fun _ => Converse.Sending context initial original context.items) := by
  unfold prelude
  exact CompletionCuts.Ensures.bind
    (Converse.sending_passive context initial original context.items _ (indexed_marker_checked context)
      (fun _ _ w complete => Converse.marker_complete context.pid context.items complete w))
    (fun _ => CompletionCuts.Ensures.bind
      (Converse.sending_passive context initial original context.items _
        (indexed_traversal_checked context (.sending context.items))
        (fun _ _ w complete => Converse.traversal_complete context.pid complete w))
      (fun _ => Converse.sending_passive context initial original context.items _
        (indexed_authenticated_checked context (.sending context.items))
        (fun _ _ w complete => Converse.authenticated_complete context.pid complete w)))

theorem scoped_iteration_run
    (before : runPrefix (prelude context) w (history ++ [entered context history]) = (.ok ((),u),middle))
    (iterations : runPrefix (sendLoop CausalJournal.completionOps context.pid done false) u middle =
      (.ok (next,v),cutHistory)) :
    runPrefix (scopedIterationPrefix context done) w history = (.ok (next,v),cutHistory) := by
  change runPrefix (do
    emitPrefix (entered context history)
    prelude context
    sendLoop CausalJournal.completionOps context.pid done false) w history = _
  rw [runPrefix_bind,runPrefix_emit]
  simp only []
  rw [runPrefix_bind,before]
  exact iterations

theorem scoped_loop_failed
    (before : Converse.Sending context initial original context.items history w)
    (prepared : runPrefix (prelude context) w (history ++ [entered context history]) = (.ok ((),u),middle))
    (failed : runPrefix (sendLoop CausalJournal.completionOps context.pid context.items false) u middle =
      (.error reason,last)) :
    runPrefix (CompletionEffects.completeScoped CausalJournal.Event.scope CausalSources.Cause.completion
      CausalJournal.completionOps context.pid context.items) w history = (.error reason,last) ∧
    ∃ done skb rest next v cutHistory ledger debts,
      context.items = done ++ (skb :: rest) ∧
      runPrefix (scopedIterationPrefix context done) w history = (.ok (next,v),cutHistory) ∧
      SendSettlements context initial original ledger debts ∧
      Nonempty (IterationStop context skb rest next v cutHistory ledger debts reason last) := by
  have atScope := before.append [entered context history]
    (by intro event member; cases List.mem_singleton.mp member; rfl)
    (by intro event member; cases List.mem_singleton.mp member; intro position; rfl)
  obtain ⟨_,_,atLoop⟩ := prelude_checked context initial original w (history ++ [entered context history]) atScope
  rw [prepared] at atLoop
  have stopped := loop_failed atLoop failed
  obtain ⟨done,skb,rest,next,v,cutHistory,ledger,debts,shape,iterations,trace,cut⟩ := stopped.iteration_prefix
  refine ⟨?_,done,skb,rest,next,v,cutHistory,ledger,debts,shape,scoped_iteration_run prepared iterations,trace,cut⟩
  have inner : runPrefix (CompletionEffects.completeWith CausalJournal.completionOps
      context.pid context.items) w (history ++ [entered context history]) = (.error reason,last) := by
    rw [complete_prelude_factor,runPrefix_bind,prepared]
    simp only [runPrefix_bind,failed]
  unfold CompletionEffects.completeScoped
  rw [CausalScope.prefix_run]
  dsimp only [entered] at inner
  rw [inner]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Sending
