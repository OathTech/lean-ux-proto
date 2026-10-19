import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionFrontier
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryCarrier

/-! The completion cursor and the global entry bundle share explicit ledger
and debt indices. An independently chosen existential completion state cannot
be combined with a different global ledger to justify staged disposal. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open RetirementSecurity

structure Cursor (context : Context) (phase : Phase) (history : List CausalJournal.Event)
    (ledger : Ledger) (debts : List CleanupDebt) : Prop where
  step : Staged.Obligations.Step context.initialLedger ledger
  recorded : ∀ binding ∈ context.bindings, binding.recorded history
  remaining : phase.remaining.IsSuffix context.items
  assigned : phase.assigned context ledger debts

structure Owned (context : Context) (phase : Phase) (history : List CausalJournal.Event)
    (ledger : Ledger) (debts : List CleanupDebt) (w : World) : Prop where
  cursor : Cursor context phase history ledger debts
  entry : StagedEntry.Inv history ledger debts
    (⟨.selected,context.pid,phase.active context⟩ :: context.locals) w.wg
  domain : births history = context.births

/-- Forgetting semantic entry facts preserves the exact ledger and debt
witnesses. This direction never recovers entry facts from an erased state. -/
theorem Owned.state (before : Owned context phase history ledger debts w) :
    State context phase history w := by
  refine ⟨ledger,debts,before.cursor.step,⟨before.entry.core.physical,?_⟩,
    before.cursor.recorded,before.cursor.remaining,before.cursor.assigned,
    before.entry.coverage,before.entry.inventory⟩
  rw [← before.domain]
  exact before.entry.core.valid

theorem Binding.pending_frame {binding : Binding} (frame : AllocatedFrame ledger after)
    (before : binding.pending ledger) : binding.pending after :=
  (frame.pending _ _ _).mpr before

theorem Binding.debt_frame {binding : Binding} (frame : AllocatedFrame ledger after)
    (before : binding.debt ledger debts) : binding.debt after debts := by
  obtain ⟨outcome,member,terminal⟩ := before
  exact ⟨outcome,member,frame.terminal _ _ terminal⟩

theorem Binding.terminal_frame {binding : Binding} (frame : AllocatedFrame ledger after)
    (before : binding.terminal ledger) : binding.terminal after := by
  obtain ⟨outcome,terminal⟩ := before
  exact ⟨outcome,frame.terminal _ _ terminal⟩

/-- A staged-ticket settlement preserves the completion's pending allocation
bindings and already chosen first terminals, including their cleanup debts. -/
theorem Cursor.allocated_frame (before : Cursor context phase history ledger debts)
    (step : Staged.Obligations.Step ledger after) (frame : AllocatedFrame ledger after) :
    Cursor context phase history after debts := by
  refine ⟨before.step.trans step,before.recorded,before.remaining,?_⟩
  intro binding member
  have assigned := before.assigned binding member
  cases phase with
  | sending remaining =>
    exact ⟨fun present => Binding.pending_frame frame (assigned.1 present),
      fun absent => Binding.debt_frame frame (assigned.2 absent)⟩
  | freeing remaining =>
    exact ⟨Binding.terminal_frame frame assigned.1,fun present => Binding.debt_frame frame (assigned.2 present)⟩

theorem Cursor.append (before : Cursor context phase history ledger debts)
    (suffix : List CausalJournal.Event) : Cursor context phase (history ++ suffix) ledger debts :=
  ⟨before.step,fun binding member => (before.recorded binding member).append suffix,
    before.remaining,before.assigned⟩

/-- The new entry bundle is indexed by the actual successor ledger, so a
caller cannot discharge this join with an unrelated existential state. -/
theorem Owned.advance (before : Owned context phase history ledger debts w)
    (step : Staged.Obligations.Step ledger after) (frame : AllocatedFrame ledger after)
    (suffix : List CausalJournal.Event)
    (entry : StagedEntry.Inv (history ++ suffix) after debts
      (⟨.selected,context.pid,phase.active context⟩ :: context.locals) v.wg)
    (domain : births (history ++ suffix) = births history) :
    Owned context phase (history ++ suffix) after debts v :=
  ⟨(before.cursor.allocated_frame step frame).append suffix,entry,domain.trans before.domain⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
