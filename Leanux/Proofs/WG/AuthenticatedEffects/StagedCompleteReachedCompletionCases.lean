import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCompletionFinish

/-! Unconditional classification of an actual scoped-completion failure.
Each constructor retains the successful native prefixes and the matched
ledger/debts at its failed prelude, loop iteration or finishing callback. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Completion
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch Staged.Obligations StagedTerminalComplete
variable {initial : Ledger}

inductive ScopedStop (context : Context) (initial : Ledger) (original : List CleanupDebt)
    (w : World) (history : List CausalJournal.Event) (reason : Stop) (last : List CausalJournal.Event) : Prop where
  | prelude (ledger : Ledger) (debts : List CleanupDebt)
      (trace : SendSettlements context initial original ledger debts)
      (cut : PreludeStop context w (history ++ [Sending.entered context history]) ledger debts reason last)
  | loop (u : World) (middle : List CausalJournal.Event)
      (prepared : runPrefix (Sending.prelude context) w (history ++ [Sending.entered context history]) =
        (.ok ((),u),middle))
      (cut : Sending.LoopStop context initial original context.items false u middle reason last)
  | finish (u : World) (middle : List CausalJournal.Event)
      (prepared : runPrefix (Sending.prelude context) w (history ++ [Sending.entered context history]) =
        (.ok ((),u),middle))
      (sent : Bool) (v : World) (after : List CausalJournal.Event)
      (looped : runPrefix (sendLoop CausalJournal.completionOps context.pid context.items false) u middle =
        (.ok (sent,v),after))
      (ledger : Ledger) (debts : List CleanupDebt)
      (trace : SendSettlements context initial original ledger debts)
      (cut : FinishStop context sent v after ledger debts reason last)

theorem scoped_failed
    (before : Converse.Sending context initial original context.items history w)
    (failed : runPrefix (CompletionEffects.completeScoped CausalJournal.Event.scope CausalSources.Cause.completion
      CausalJournal.completionOps context.pid context.items) w history = (.error reason,last)) :
    ScopedStop context initial original w history reason last := by
  let start := history ++ [Sending.entered context history]
  have atScope := before.append [Sending.entered context history]
    (by intro event member; cases List.mem_singleton.mp member; rfl)
    (by intro event member; cases List.mem_singleton.mp member; intro position; rfl)
  change Converse.Sending context initial original context.items start w at atScope
  have inner : runPrefix (CompletionEffects.completeWith CausalJournal.completionOps context.pid context.items)
      w start = (.error reason,last) := by
    unfold CompletionEffects.completeScoped at failed
    rw [CausalScope.prefix_run] at failed
    cases performed : runPrefix (CompletionEffects.completeWith CausalJournal.completionOps context.pid context.items)
        w start with
    | mk result tail =>
      have equation := performed
      dsimp only [start,Sending.entered] at equation
      rw [equation] at failed
      cases result with
      | error stop => cases failed; rfl
      | ok out => cases failed
  rw [Sending.complete_prelude_factor,runPrefix_bind] at inner
  cases prepared : runPrefix (Sending.prelude context) w start with
  | mk result middle =>
    rw [prepared] at inner
    cases result with
    | error stop =>
      cases inner
      obtain ⟨ledger,debts,trace,owned,_,complete⟩ := atScope
      obtain ⟨cut⟩ := prelude_failed owned complete prepared
      exact .prelude ledger debts trace cut
    | ok out =>
      obtain ⟨ignored,u⟩ := out
      cases ignored
      obtain ⟨_,_,atLoop⟩ := Sending.prelude_checked context initial original w start atScope
      rw [prepared] at atLoop
      change runPrefix (do
        let sent ← sendLoop CausalJournal.completionOps context.pid context.items false
        finish CausalJournal.completionOps context.pid sent) u middle = _ at inner
      rw [runPrefix_bind] at inner
      cases looped : runPrefix (sendLoop CausalJournal.completionOps context.pid context.items false) u middle with
      | mk result after =>
        rw [looped] at inner
        cases result with
        | error stop =>
          cases inner
          exact .loop u middle prepared (Sending.loop_failed atLoop looped)
        | ok out =>
          obtain ⟨sent,v⟩ := out
          obtain ⟨_,_,atFinish⟩ := Converse.sendLoop_checked context initial original context.items false u middle atLoop
          rw [looped] at atFinish
          obtain ⟨ledger,debts,trace,owned,_,complete⟩ := atFinish
          obtain ⟨cut⟩ := finish_failed owned complete inner
          exact .finish u middle prepared sent v after looped ledger debts trace cut

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Completion
