import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteSelectedSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRestore
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteTimerQueue

/-! The real no-key and invalid-key continuation restores its selected tickets
before queued initiation. Any final queued repayment uses counted accounting
on the resulting ledger; it is not treated as terminal-quiet. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteSelected
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity
open AllocatedObligation CausalJournal CompleteCarrier

theorem no_key (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat)
    (keypair : Option KeypairId) (invalid : Bool) (Safe : List Event → Prop)
    (frontier : ∀ h, Active ledger debts generation pid peer position h → Safe h)
    (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h) :
    StatePrefixEnsures (Ready ledger debts locals generation pid peer position) Safe
      (HeldSource.noKey pid peer keypair invalid) (fun _ => Carrier debts locals) := by
  unfold HeldSource.noKey
  rw [RestoreEntry.no_key_factor]
  apply StatePrefixEnsures.bind (before_restore frontier peer.staged keypair invalid)
  intro _
  apply StatePrefixEnsures.bind (restore ledger debts locals generation pid peer position Safe (accountSafe _))
  intro _ w a h before
  exact CompleteTimerQueue.queued Safe accountSafe pid false w a h ⟨_,before⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteSelected
