import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixStagingSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixAdmissionFront
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixAdmissionKeepalive
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixPassive

/-! Actual keepalive and routed transmission compose admission with closed
staging and counted repayment. Every emitted journal prefix is certified;
native silent-interval correspondence remains an independent obligation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Transmit
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity RetirementSecurity CausalJournal CompleteCarrier
variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}

theorem account (ledger : Staged.Obligations.Ledger) (h : List Event) (w : WGWorld)
    (before : Accounted h ledger debts locals w) : CompleteProduct.Safe h :=
  ⟨debts,.accounted ledger locals h w before⟩

theorem keepalive (pid : PeerId) : Passive.Checked debts locals CompleteProduct.Safe
    (Driver.keepaliveObserved hooks pid) := by
  unfold Driver.keepaliveObserved
  apply StateEnsures.bind (Admission.keepalive pid CompleteProduct.Safe account)
  intro ready
  cases ready
  · exact Passive.pure_checked CompleteProduct.Safe account ()
  · exact Staging.staging debts locals pid

theorem transmit (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    Passive.Checked debts locals CompleteProduct.Safe (Driver.transmitObserved hooks family addr packets mtu) := by
  unfold Driver.transmitObserved
  apply StateEnsures.bind (Admission.front ⟨family,addr,packets,mtu⟩ CompleteProduct.Safe account)
  intro result
  cases result with
  | error err=>exact Passive.pure_checked CompleteProduct.Safe account err
  | ok pid=>
    exact StateEnsures.bind (Staging.staging debts locals pid) (fun _=>
      StateEnsures.bind (Disposal.original (some pid) CompleteProduct.Safe account)
        (fun _=>Passive.pure_checked CompleteProduct.Safe account 0))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Transmit
