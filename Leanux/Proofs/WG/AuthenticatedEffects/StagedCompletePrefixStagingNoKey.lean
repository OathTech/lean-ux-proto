import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixStagingQueue

/-! The original no-key continuation accounts every nonce/refusal prefix,
restores the exact selected ledger, and then invokes counted queued work. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Staging
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open CompleteCarrier AllocatedObligation

theorem no_key (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat)
    (keypair : Option KeypairId) (invalid : Bool) :
    StateEnsures (CompleteSelected.Ready ledger debts locals generation pid peer position)
      CompleteProduct.Safe (HeldSource.noKey pid peer keypair invalid) (fun _=>Carrier debts locals) := by
  unfold HeldSource.noKey
  rw [RestoreEntry.no_key_factor]
  apply StateEnsures.bind (before_restore peer.staged keypair invalid)
  intro _
  apply StateEnsures.bind (restore ledger debts locals generation pid peer position)
  intro _
  exact StatePrefixEnsures.consequence (queued pid false)
    (fun _ _ _ before=>⟨⟨_,before.1⟩,before.2⟩) (fun _ _ _ _ after=>after)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Staging
