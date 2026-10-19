import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixStagingSingle
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRestore

/-! Actual selected restoration supplies its exact successor ledger. Its one
completed native receipt is certified separately from the incoming history. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Staging
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open CompleteCarrier HandshakeSecurity.StagedConservation

theorem ready_safe (before : CompleteSelected.Ready ledger debts locals generation pid peer position h w a) :
    CompleteProduct.Safe h :=
  ⟨debts,.selected ledger generation pid peer position h before.active⟩

/-- The full selected carrier includes its recorded native take and packet
ownership. Normal return retains precisely the restored ledger, while every
actual output prefix has its logical safety certificate, even on Stop. -/
theorem restore (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (locals : List TxLocalBatch) (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat) :
    StateEnsures (CompleteSelected.Ready ledger debts locals generation pid peer position) CompleteProduct.Safe
      (CausalJournal.stagedRestore pid peer.staged)
      (fun _ h w _=>Accounted h (HeldFrontier.restoredLedger ledger generation pid peer position) debts locals w) := by
  apply native_receipt (Restore.nativeRestore pid peer.staged)
    (fun run=>Event.stagedRestored ⟨pid,peer.staged,run⟩)
  · exact CompleteSelected.restore ledger debts locals generation pid peer position CompleteProduct.Safe
      (fun h w before=>⟨debts,.accounted _ locals h w before⟩)
  · intro h w a before
    exact ready_safe before

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Staging
