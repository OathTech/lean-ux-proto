import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePollSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteTransmit
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteTimerCallbacks

/-! Concrete native poll and stack callbacks use the actual paired staging
and transmit proofs. Failed selected staging retains its active native cut;
that case is not converted into an idle Accounted witness. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePollConcrete
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal CompletePoll
open CompleteCarrier (Accounted)
variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}

theorem safe (h : List Event) (w : World) (before : Carrier debts locals h w) : CompleteTransmit.Safe debts h := by
  obtain ⟨ledger,accounted⟩ := before
  exact CompleteTransmit.Safe.accounted ledger locals h w.wg accounted

/-- Every actual stack reply preserves the paired ledger through the concrete
routed transmit source; selected stopped cuts remain explicitly certified. -/
theorem stack (bytes : List UInt8) : Checked debts locals (CompleteTransmit.Safe debts)
    (Driver.stackObserved hooks bytes) :=
  CompleteStack.stack (CompleteTransmit.Safe debts)
    (fun ledger => CompleteTransmit.Safe.accounted ledger locals) CompleteTransmit.transmit bytes

/-- The complete original native poll and tagged GRO path preserves Entry
and terminal completeness on the same ledger with no assumed source callback.
A stopped selected-staging prefix retains its actual active cut. -/
theorem native_poll (pid : PeerId) (budget : Nat) : Checked debts locals (CompleteTransmit.Safe debts)
    (Driver.nativePollObserved hooks pid budget) :=
  CompletePollSource.native_poll (CompleteTransmit.Safe debts)
    (fun ledger => CompleteTransmit.Safe.accounted ledger locals)
    CompleteTransmit.staging CompleteTransmit.transmit pid budget

/-- All five original timer callbacks preserve paired accounting with the
actual keepalive admission and staging source contract discharged. -/
theorem timer (pid : PeerId) (timer : PeerTimer) : CompletePassive.Checked debts locals (CompleteTransmit.Safe debts)
    (Driver.timerObserved hooks pid timer) :=
  CompleteTimerCallbacks.callback (CompleteTransmit.Safe debts)
    (fun ledger => CompleteTransmit.Safe.accounted ledger locals) pid timer (CompleteTransmit.keepalive pid)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePollConcrete
