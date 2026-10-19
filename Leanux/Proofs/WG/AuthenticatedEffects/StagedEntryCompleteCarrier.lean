import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryPassive
import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalCompleteLedgerFrames

/-! Forward state conservation and converse receipt accounting share one
ledger. Existing native frames are reusable; extending the converse needs
terminal-quiet history, a stronger obligation than birth-quiet history. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteCarrier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open StagedTerminalComplete

structure Accounted (history : List Event) (ledger : Ledger)
    (debts : List AllocatedObligation.CleanupDebt) (locals : List TxLocalBatch) (w : WGWorld) : Prop where
  entry : Inv history ledger debts locals w
  complete : Complete history ledger

def Safe (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (locals : List TxLocalBatch) (history : List Event) : Prop :=
  ∃ w, Accounted history ledger debts locals w

def Carrier (debts : List AllocatedObligation.CleanupDebt) (locals : List TxLocalBatch)
    (history : List Event) (w : WGWorld) (_ : Ambient) : Prop :=
  ∃ ledger, Accounted history ledger debts locals w

theorem initial (net bare : Bool) : Accounted [] [] [] [] (Runner.initialWG net bare) :=
  ⟨StagedEntry.initial net bare,Complete.empty []⟩

theorem Accounted.same_view (before : Accounted history ledger debts locals w)
    (same : StagedEntry.view v = StagedEntry.view w) : Accounted history ledger debts locals v :=
  ⟨before.entry.same_view same,before.complete⟩

theorem Accounted.append_quiet (before : Accounted history ledger debts locals w)
    (suffix : List Event) (births : ∀ event ∈ suffix, birthPackets event = [])
    (terminals : ∀ event ∈ suffix, Quiet event) : Accounted (history ++ suffix) ledger debts locals w :=
  ⟨Queued.Inv.history before.entry suffix births,before.complete.append_quiet terminals⟩

abbrev Checked (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (locals : List TxLocalBatch) (action : WGPrefix Event α) : Prop :=
  StatePrefixPreserves (fun h w _ => Accounted h ledger debts locals w) (Safe ledger debts locals) action

theorem native (action : WG.M α) (frame : SameView StagedEntry.view action) :
    Checked ledger debts locals (liftWGPrefix action) := by
  apply StatePrefixEnsures.lift _ (fun _ w _ before => ⟨w,before⟩)
  intro h w a value v b before run
  exact before.same_view ((ProjectedAction.iff_run_ambient _ _ _).mp frame w a value v b run)

/-- A fixed-ledger source contract can be reused when its actual suffix has
no terminal demand. The failure witness retains the same complete history,
without inventing a final native world at Stop. -/
theorem passive (action : WGPrefix Event α) (checked : Passive.Checked ledger debts locals action)
    (quiet : ∀ w a h, ∃ suffix, (runWGPrefix action w a h).2 = h ++ suffix ∧
      ∀ event ∈ suffix, Quiet event) : Checked ledger debts locals action := by
  intro w a h before
  obtain ⟨suffix,extended,terminals⟩ := quiet w a h
  obtain ⟨_,_,safe,kept⟩ := checked w a h before.entry
  have complete : Complete (runWGPrefix action w a h).2 ledger := by
    rw [extended]
    exact before.complete.append_quiet terminals
  refine ⟨suffix,extended,?_,?_⟩
  · obtain ⟨cut,entry⟩ := safe
    exact ⟨cut,entry,complete⟩
  · cases result : (runPrefix (action.run w) a h).1 with
    | error stop => trivial
    | ok out =>
      obtain ⟨⟨value,v⟩,b⟩ := out
      rw [result] at kept
      exact ⟨kept,complete⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteCarrier
