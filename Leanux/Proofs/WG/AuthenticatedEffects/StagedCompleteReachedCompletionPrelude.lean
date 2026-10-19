import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCompletionPassive

/-! The completion marker is total. Each early Stop therefore follows the
literal marker prefix or marker-plus-traversal prefix of the same execution. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Completion
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch Staged.Obligations StagedTerminalComplete

inductive PreludeStage where
  | traversal | authenticated

def preludeSite (context : Context) : PreludeStage → Site
  | .traversal => .traversal context.pid
  | .authenticated => .authenticated context.pid

def preludePrefix (context : Context) : PreludeStage → PrefixM CausalJournal.Event Unit
  | .traversal => CausalJournal.completionOps.completion context.pid context.items
  | .authenticated => do
      CausalJournal.completionOps.completion context.pid context.items
      CausalJournal.completionOps.traversal context.pid

structure PreludeStop (context : Context) (w : World) (history : List CausalJournal.Event)
    (ledger : Ledger) (debts : List CleanupDebt) (reason : Stop) (last : List CausalJournal.Event) where
  stage : PreludeStage
  world : World
  before : List CausalJournal.Event
  reached : runPrefix (preludePrefix context stage) w history = (.ok ((),world),before)
  cut : PassiveStop context (.sending context.items) (preludeSite context stage)
    world before ledger debts reason last

theorem marker_run (context : Context) (w : World) (history : List CausalJournal.Event) :
    runPrefix (CausalJournal.completionOps.completion context.pid context.items) w history =
      (.ok ((),w),history ++ [.old (.disposition (.completion context.pid context.items))]) :=
  focusPrefix_suffix FirstTerminal.encode CausalJournal.completion?
    (emitPrefix (.disposition (.completion context.pid context.items))) w history (.ok ((),w))
    [.disposition (.completion context.pid context.items)] (runPrefix_emit _ w _)

theorem prelude_failed
    (before : Owned context (.sending context.items) history ledger debts w)
    (complete : Complete history ledger)
    (failed : runPrefix (Sending.prelude context) w history = (.error reason,last)) :
    Nonempty (PreludeStop context w history ledger debts reason last) := by
  let marked := history ++ [CausalJournal.Event.old (.disposition (.completion context.pid context.items))]
  have marker := marker_run context w history
  have ⟨atMark,pairedMark⟩ := passive_returned before (indexed_marker_checked context ledger debts)
    (Converse.marker_complete context.pid context.items complete w) marker
  change Owned context (.sending context.items) marked ledger debts w at atMark
  change Complete marked ledger at pairedMark
  simp only [Sending.prelude,runPrefix_bind,marker] at failed
  cases traversed : runPrefix (CausalJournal.completionOps.traversal context.pid) w marked with
  | mk result middle =>
    rw [traversed] at failed
    cases result with
    | error stop =>
      cases failed
      have cut := passive_failed (site := .traversal context.pid) atMark
        (indexed_traversal_checked context (.sending context.items) ledger debts)
        (Converse.traversal_complete context.pid pairedMark w) traversed
      exact ⟨⟨.traversal,w,marked,marker,cut⟩⟩
    | ok out =>
      obtain ⟨ignored,v⟩ := out
      cases ignored
      have ⟨atTraversal,pairedTraversal⟩ := passive_returned atMark
        (indexed_traversal_checked context (.sending context.items) ledger debts)
        (Converse.traversal_complete context.pid pairedMark w) traversed
      have cut := passive_failed (site := .authenticated context.pid) atTraversal
        (indexed_authenticated_checked context (.sending context.items) ledger debts)
        (Converse.authenticated_complete context.pid pairedTraversal v) failed
      refine ⟨⟨.authenticated,v,middle,?_,cut⟩⟩
      rw [preludePrefix,runPrefix_bind,marker]
      exact traversed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Completion
