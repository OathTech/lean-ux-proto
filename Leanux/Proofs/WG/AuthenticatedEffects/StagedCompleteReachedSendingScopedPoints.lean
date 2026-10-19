import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSendingPoints
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSendingScoped
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCompletionPrefixes

/-! Actual completion-scope entry and its original successful send-list
prefix reach each send callback. The resulting point and continuation are
valid independently of whether the remaining completion succeeds or stops. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Sending
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch Staged.Obligations StagedTerminalComplete
variable {initial : Ledger}

structure ScopedLoopPoint (context : Context) (w : World) (history : List CausalJournal.Event)
    (rest : List SkbId) (next : Bool) (v : World) (after : List CausalJournal.Event) where
  loopWorld : World
  loopHistory : List CausalJournal.Event
  prepared : runPrefix (prelude context) w (history++[entered context history])=
    (.ok ((),loopWorld),loopHistory)
  loop : LoopPoint context.pid context.items false loopWorld loopHistory rest next v after

theorem ScopedLoopPoint.entry
    (point : ScopedLoopPoint context w history rest next v after)
    (before : Converse.Sending context initial original context.items history w) :
    Converse.Sending context initial original context.items point.loopHistory point.loopWorld := by
  have marked := before.append [entered context history]
    (by intro event member; cases List.mem_singleton.mp member; rfl)
    (by intro event member; cases List.mem_singleton.mp member; intro position; rfl)
  obtain ⟨_,_,checked⟩ := prelude_checked context initial original w (history++[entered context history]) marked
  simpa only [point.prepared] using checked

theorem ScopedLoopPoint.carrier
    (point : ScopedLoopPoint context w history rest next v after)
    (before : Converse.Sending context initial original context.items history w) :
    Converse.Sending context initial original rest after v := point.loop.carrier (point.entry before)

theorem ScopedLoopPoint.literal (point : ScopedLoopPoint context w history rest next v after) :
    runPrefix (scopedIterationPrefix context point.loop.done) w history=(.ok (next,v),after) :=
  scoped_iteration_run point.prepared point.loop.performed

theorem ScopedLoopPoint.continuation (point : ScopedLoopPoint context w history rest next v after) :
    runPrefix (CompletionEffects.completeScoped CausalJournal.Event.scope CausalSources.Cause.completion
      CausalJournal.completionOps context.pid context.items) w history =
      match runPrefix (do
        let sent ← sendLoop CausalJournal.completionOps context.pid rest next
        finish CausalJournal.completionOps context.pid sent) v after with
      | (.error reason,last) => (.error reason,last)
      | (.ok value,last) => (.ok value,last++[.scope (.exited history.length)]) := by
  unfold CompletionEffects.completeScoped
  rw [CausalScope.prefix_run]
  rw [complete_prelude_factor]
  have prepared := point.prepared
  dsimp only [entered] at prepared
  rw [runPrefix_bind,prepared]
  simp only
  rw [runPrefix_bind,point.loop.continuation]
  rw [runPrefix_bind]
  cases runPrefix (sendLoop CausalJournal.completionOps context.pid rest next) v after with
  | mk result last =>
      cases result with
      | error reason => rfl
      | ok value =>
          obtain ⟨sent,u⟩ := value
          dsimp only
          cases runPrefix (finish CausalJournal.completionOps context.pid sent) u last with
          | mk outcome events =>
              cases outcome with
              | error reason => rfl
              | ok value =>
                  obtain ⟨result,u⟩ := value
                  cases result
                  rfl

theorem ScopedLoopPoint.send_entry
    (point : ScopedLoopPoint context w history (skb::rest) next v after)
    (before : Converse.Sending context initial original context.items history w) :
    ∃ ledger debts packet u middle,
      SendSettlements context initial original ledger debts ∧
      runPrefix (Completion.sourcePrefix context (.packet point.loop.done skb)) w history=(.ok ((),u),middle) ∧
      Owned context (.sending (skb::rest)) middle ledger debts u ∧
      Complete middle ledger ∧ PacketAt skb packet u := by
  obtain ⟨ledger,debts,packet,u,middle,trace,reached,owned,complete,resident⟩ :=
    point.loop.send_entry (point.entry before)
  refine ⟨ledger,debts,packet,u,middle,trace,?_,owned,complete,resident⟩
  simp only [Completion.sourcePrefix,runPrefix_bind,point.literal,reached,runPrefix_pure]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Sending
