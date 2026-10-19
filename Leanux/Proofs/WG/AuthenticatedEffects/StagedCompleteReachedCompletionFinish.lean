import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCompletionPrelude

/-! The two final branch markers are total. A stopped finish therefore has
the actual data-sent or fresh-key callback entry after its literal guard prefix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Completion
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch Staged.Obligations StagedTerminalComplete

inductive FinishStage where
  | dataSent | fresh

def finishSite (context : Context) : FinishStage → Site
  | .dataSent => .dataSent context.pid
  | .fresh => .fresh context.pid

def finishGuard (dataSent : Bool) : PrefixM CausalJournal.Event Bool := do
  _ ← CausalJournal.completionOps.step (branch .doneSkbIterate false)
  CausalJournal.completionOps.step (branch .doneDataSent dataSent)

def finishTail (context : Context) (dataSent : Bool) : PrefixM CausalJournal.Event Unit := do
  if dataSent then CausalJournal.completionOps.dataSent context.pid
  CausalJournal.completionOps.fresh context.pid

def finishPrefix (context : Context) (dataSent : Bool) : FinishStage → PrefixM CausalJournal.Event Unit
  | .dataSent => CompletionBatch.discard (finishGuard dataSent)
  | .fresh => do
      let sent ← finishGuard dataSent
      if sent then CausalJournal.completionOps.dataSent context.pid

structure FinishStop (context : Context) (dataSent : Bool) (w : World) (history : List CausalJournal.Event)
    (ledger : Ledger) (debts : List CleanupDebt) (reason : Stop) (last : List CausalJournal.Event) where
  stage : FinishStage
  enabled : stage = .dataSent → dataSent = true
  world : World
  before : List CausalJournal.Event
  reached : runPrefix (finishPrefix context dataSent stage) w history = (.ok ((),world),before)
  cut : PassiveStop context (.sending []) (finishSite context stage)
    world before ledger debts reason last

theorem finish_factor (context : Context) (dataSent : Bool) :
    finish CausalJournal.completionOps context.pid dataSent =
      finishGuard dataSent >>= finishTail context := by
  simp only [finish,finishGuard,bind_assoc]
  congr 1

theorem guard_total (dataSent : Bool) (w : World) (history : List CausalJournal.Event) :
    ∃ v, runPrefix (finishGuard dataSent) w history = (.ok (dataSent,v),history) ∧ v.wg = w.wg := by
  simp only [finishGuard,runPrefix_bind,branch_run]
  exact ⟨_,rfl,rfl⟩

theorem finish_failed
    (before : Owned context (.sending []) history ledger debts w)
    (complete : Complete history ledger)
    (failed : runPrefix (finish CausalJournal.completionOps context.pid dataSent) w history = (.error reason,last)) :
    Nonempty (FinishStop context dataSent w history ledger debts reason last) := by
  obtain ⟨u,guards,same⟩ := guard_total dataSent w history
  have atGuard := before.sameWG same
  rw [finish_factor,runPrefix_bind,guards] at failed
  cases dataSent with
  | false =>
    simp only [finishTail,Bool.false_eq_true,↓reduceIte] at failed
    have cut := passive_failed (site := .fresh context.pid) atGuard
      (indexed_fresh_checked context (.sending []) ledger debts)
      (Converse.fresh_complete context.pid atGuard complete) failed
    refine ⟨⟨.fresh,(by intro impossible; cases impossible),u,history,?_,cut⟩⟩
    rw [finishPrefix,runPrefix_bind,guards]
    rfl
  | true =>
    simp only [finishTail,↓reduceIte,runPrefix_bind] at failed
    cases performed : runPrefix (CausalJournal.completionOps.dataSent context.pid) u history with
    | mk result middle =>
      rw [performed] at failed
      cases result with
      | error stop =>
        cases failed
        have cut := passive_failed (site := .dataSent context.pid) atGuard
          (indexed_dataSent_checked context (.sending []) ledger debts)
          (Converse.dataSent_complete context.pid complete u) performed
        refine ⟨⟨.dataSent,(fun _ => rfl),u,history,?_,cut⟩⟩
        rw [finishPrefix,CompletionBatch.discard,runPrefix_bind,guards]
        rfl
      | ok out =>
        obtain ⟨ignored,v⟩ := out
        cases ignored
        have ⟨atData,pairedData⟩ := passive_returned atGuard
          (indexed_dataSent_checked context (.sending []) ledger debts)
          (Converse.dataSent_complete context.pid complete u) performed
        have cut := passive_failed (site := .fresh context.pid) atData
          (indexed_fresh_checked context (.sending []) ledger debts)
          (Converse.fresh_complete context.pid atData pairedData) failed
        refine ⟨⟨.fresh,(by intro impossible; cases impossible),v,middle,?_,cut⟩⟩
        rw [finishPrefix,runPrefix_bind,guards]
        exact performed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Completion
