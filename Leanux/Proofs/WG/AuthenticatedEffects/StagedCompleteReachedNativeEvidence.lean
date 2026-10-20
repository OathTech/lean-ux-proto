import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConfigConcreteInitialized
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNativePartition

/-! Concrete phase evidence over the WG projection. Ordinary accounts,
selected/allocation phases and the named pending receipts remain distinct.
This type does not turn an unemitted receipt into a journal event. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NativeAccounting
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Staged.Obligations CompleteCarrier
abbrev History := List Event

inductive Evidence : History → WGWorld → Prop where
  | accounted (ledger : Ledger) (account : Accounted h ledger [] [] w) : Evidence h w
  | purge (pending : Timer.Points.Purge.Awaiting h w) : Evidence h w.wg
  | peer (ledger : Ledger) (proof : PeerRetirement.Points.Evidence ledger [] [] h w) : Evidence h w
  | staging (ledger : Ledger) (proof : StagingExpanded.Evidence ledger [] [] h w a) : Evidence h w
  | front (ledger : Ledger) (proof : FrontCuts.Evidence ledger [] [] h w a) : Evidence h w
  | keepalive (ledger : Ledger) (proof : KeepaliveExpanded.Evidence ledger [] [] pid w a h middle v b) :
      Evidence middle v
  | transmit (ledger : Ledger) (pid : PeerId) (proof : TxConcrete.Evidence ledger [] pid h w) : Evidence h w.wg

theorem Evidence.of_account (before : Lifecycle.Points.Account h w) : Evidence h w.wg := by
  obtain ⟨ledger,account⟩:=before
  exact .accounted ledger account

theorem Evidence.of_carrier (before : CompleteProduct.Carrier h w) : Evidence h w.wg :=
  .of_account before.1

theorem Evidence.of_encryption (before : EncryptionCallback.Evidence ledger [] [] h w) : Evidence h w.wg := by
  cases before with
  | accounted account=>exact .accounted ledger account
  | release proof=>exact .peer ledger proof

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NativeAccounting
