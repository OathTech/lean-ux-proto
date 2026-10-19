import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPhaseCoverage

/-! Phase evidence keeps a successor of the original ticket ledger. Silent
queue writes have explicit pending receipts, rather than an idle account in
a world whose native ownership has already changed. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Staged.Obligations CompleteCarrier Staging.Points
set_option maxHeartbeats 600000

inductive Evidence (root : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (locals : List RetirementSecurity.TxLocalBatch) : List Event → WGWorld → Ambient → Prop where
  | accounted (current : Ledger) (steps : Staged.Obligations.Step root current)
      (account : Accounted h current debts locals w) : Evidence root debts locals h w a
  | selected (current : Ledger) (steps : Staged.Obligations.Step root current)
      (ready : CompleteSelected.Ready current debts locals generation pid peer position h w a) :
      Evidence root debts locals h w a
  | taking (current : Ledger) (steps : Staged.Obligations.Step root current)
      (cut : PendingTake h current debts locals pid w a peer v b) : Evidence root debts locals h v b
  | restoring (current : Ledger) (steps : Staged.Obligations.Step root current)
      (cut : PendingRestore h current debts locals generation pid peer position w a v) :
      Evidence root debts locals h v a
  | created (assigned : Ledger) (steps : Staged.Obligations.Step root assigned)
      (live : CreatePhase.Live assigned debts locals pid items h w) : Evidence root debts locals h w a

theorem take_evidence (steps : Staged.Obligations.Step root ledger)
    (phase : TakePhase h ledger debts locals pid w a middle v b) : Evidence root debts locals middle v b := by
  cases phase with
  | entry account=>exact .accounted ledger steps account
  | pending peer cut=>exact .taking ledger steps cut

theorem restore_evidence (steps : Staged.Obligations.Step root ledger)
    (phase : RestorePhase h ledger debts locals generation pid peer position w a middle v b) :
    Evidence root debts locals middle v b := by
  cases phase with
  | entry ready=>exact .selected ledger steps ready
  | pending cut=>exact .restoring ledger steps cut
  | recorded native account ordered counter=>
    exact .accounted _ (steps.trans (transferLocation_step _ _ _)) account

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
