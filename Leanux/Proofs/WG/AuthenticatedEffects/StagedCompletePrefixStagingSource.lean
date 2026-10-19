import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixStagingSubmit
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixStagingNoKey

/-! Every actual staging journal prefix is logically accounted. The native
selection, nonce traversal, restoration, allocation and creation are all
closed source contracts. This does not identify silent native intervals or
reconstruct an unreturned world from the history-only Safe predicate. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Staging
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open CompleteCarrier AllocatedObligation

theorem staging_fixed (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch) (pid : PeerId) :
    StateEnsures (fun h w _=>Accounted h ledger debts locals w) CompleteProduct.Safe
      (Driver.stagingObserved hooks pid) (fun _=>Carrier debts locals) := by
  rw [HeldSource.staging_factor]
  apply StateEnsures.bind (selection ledger debts locals pid)
  intro selected
  cases selected with
  | none=>
    exact StateEnsures.pure () (fun _ _ _ before=>⟨ledger,before⟩)
  | some pair=>
    obtain ⟨peer,keypair⟩ := pair
    intro w a h before
    obtain ⟨after,generation,position,_,_,ready⟩ := before.1
    exact checked after debts locals generation pid peer position keypair (Carrier debts locals)
      (HeldSource.noKey pid peer) (HeldSource.submit pid)
      (no_key after debts locals generation pid peer position)
      (submit after debts locals generation pid peer position) w a h ⟨ready,before.2⟩

/-- No containing-run success or callback premise is supplied: only the
incoming full same-ledger carrier and logical certificates of its past. -/
theorem staging (debts : List CleanupDebt) (locals : List TxLocalBatch) (pid : PeerId) :
    StateEnsures (Carrier debts locals) CompleteProduct.Safe (Driver.stagingObserved hooks pid)
      (fun _=>Carrier debts locals) := by
  intro w a h before
  obtain ⟨ledger,accounted⟩ := before.1
  exact staging_fixed ledger debts locals pid w a h ⟨accounted,before.2⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Staging
