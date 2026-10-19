import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteDispose

/-! Whole actual scoped completion and cleanup preserve terminal
completeness on the same explicit source ledger. The normal and stopped
results retain the exact send trace, cleanup cut and release successor. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open TransmitSecurity.Staged.Obligations CompletionCuts StagedTerminalComplete

inductive BatchStopped (context : Context) (initial : Ledger) (key : KeypairId)
    (w : World) (history : List CausalJournal.Event) (reason : Stop)
    (last : List CausalJournal.Event) : Prop where
  | sending (failed : runPrefix
      (CompletionEffects.completeScoped CausalJournal.Event.scope CausalSources.Cause.completion
        CausalJournal.completionOps context.pid context.items) w history = (.error reason,last))
      (frontier : SendingStopped context initial [] reason last)
  | disposing (ledger : Ledger) (debts : List CleanupDebt) (cutWorld : World)
      (cutHistory : List CausalJournal.Event)
      (completed : runPrefix
        (CompletionEffects.completeScoped CausalJournal.Event.scope CausalSources.Cause.completion
          CausalJournal.completionOps context.pid context.items) w history = (.ok ((),cutWorld),cutHistory))
      (trace : SendSettlements context initial [] ledger debts)
      (owned : Owned context (.freeing context.items) cutHistory ledger debts cutWorld)
      (localDebts : LocalDebts context context.items debts)
      (complete : Complete cutHistory ledger)
      (failed : runPrefix (CausalJournal.completionOps.dispose context.pid context.items key)
        cutWorld cutHistory = (.error reason,last))
      (frontier : DisposeStopped context key ledger reason last)

def BatchReturned (context : Context) (initial : Ledger) (key : KeypairId)
    (w : World) (history last : List CausalJournal.Event) (value : Bool) (v : World) : Prop :=
  ∃ ledger debts cutWorld cutHistory,
    runPrefix (CompletionEffects.completeScoped CausalJournal.Event.scope CausalSources.Cause.completion
      CausalJournal.completionOps context.pid context.items) w history = (.ok ((),cutWorld),cutHistory) ∧
    SendSettlements context initial [] ledger debts ∧
    Owned context (.freeing context.items) cutHistory ledger debts cutWorld ∧
    LocalDebts context context.items debts ∧ Complete cutHistory ledger ∧
    runPrefix (CausalJournal.completionOps.dispose context.pid context.items key) cutWorld cutHistory =
      (.ok (value,v),last) ∧
    DisposeReturned context ledger last value v

/-- No callback contract is assumed: every send, timer, free and release
is the actual source. Stop retains its precise send or post-completion cut. -/
theorem completedAndDisposed_cases (key : KeypairId)
    (before : Owned context (.sending context.items) history ledger [] w) (complete : Complete history ledger) :
    match (runPrefix (completedAndDisposed context key) w history).1 with
    | .error reason => BatchStopped context ledger key w history reason
        (runPrefix (completedAndDisposed context key) w history).2
    | .ok (value,v) => BatchReturned context ledger key w history
        (runPrefix (completedAndDisposed context key) w history).2 value v := by
  have start := Sending.start before (LocalDebts.empty context context.items) complete
  obtain ⟨_,_,checked⟩ := completeScoped_checked context ledger [] w history start
  unfold completedAndDisposed
  rw [runPrefix_bind]
  cases completed : runPrefix
      (CompletionEffects.completeScoped CausalJournal.Event.scope CausalSources.Cause.completion
        CausalJournal.completionOps context.pid context.items) w history with
  | mk outcome cutHistory =>
    rw [completed] at checked
    cases outcome with
    | error reason => exact .sending completed checked
    | ok out =>
      obtain ⟨ignored,cutWorld⟩ := out
      cases ignored
      obtain ⟨after,debts,trace,owned,localDebts,completeCut⟩ := checked
      have ready := owned.ready_to_free
      obtain ⟨_,_,_,_,_,disposed⟩ := dispose_cases key ready localDebts completeCut
      dsimp only
      cases performed : runPrefix (CausalJournal.completionOps.dispose context.pid context.items key)
          cutWorld cutHistory with
      | mk outcome last =>
        rw [performed] at disposed
        cases outcome with
        | error reason => exact .disposing after debts cutWorld cutHistory completed trace ready localDebts completeCut performed disposed
        | ok out => exact ⟨after,debts,cutWorld,cutHistory,completed,trace,ready,localDebts,completeCut,performed,disposed⟩

theorem BatchReturned.entry
    (result : BatchReturned context initial key w history last value v) :
    ∃ after, Staged.Obligations.Step initial after ∧ StagedEntry.Inv last after [] context.locals v.wg ∧ Complete last after := by
  obtain ⟨ledger,debts,_,_,_,trace,_,_,_,_,_,after,step,_,_,entry,complete,_⟩ := result
  exact ⟨after,trace.step.trans step,entry,complete⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse
