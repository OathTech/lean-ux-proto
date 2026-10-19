import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteStaging
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteFrontChecked
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteKeepalive

/-! Concrete paired staging, keepalive and routed transmission. The history
certificate retains actual idle/creation cuts or the selected take anchor;
normal return restores the caller's debt and local-owner lists. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteTransmit
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity
open AllocatedObligation CausalJournal CompleteCarrier

inductive Safe (debts : List CleanupDebt) : List Event → Prop where
  | accounted (ledger locals h w) (kept : Accounted h ledger debts locals w) : Safe debts h
  | selected (ledger generation pid peer position h)
      (kept : CompleteSelected.Active ledger debts generation pid peer position h) : Safe debts h

theorem staging (pid : PeerId) :
    StatePrefixPreserves (Carrier debts locals) (Safe debts) (Driver.stagingObserved hooks pid) :=
  CompleteSelected.staging pid (Safe debts) Safe.accounted
    (fun ledger generation peer position h => Safe.selected ledger generation pid peer position h)

theorem pure_accounted (value : α) : StatePrefixPreserves (Carrier debts locals) (Safe debts) (pure value) :=
  StatePrefixEnsures.pure value (fun h w _ before => before.elim (fun ledger => Safe.accounted ledger locals h w))
    (fun _ _ _ before => before)

theorem keepalive (pid : PeerId) :
    StatePrefixPreserves (Carrier debts locals) (Safe debts) (Driver.keepaliveObserved hooks pid) := by
  unfold Driver.keepaliveObserved
  apply StatePrefixEnsures.bind (CompleteKeepalive.checked pid (Safe debts)
    (fun ledger => Safe.accounted ledger locals))
  intro ready
  cases ready
  · exact pure_accounted ()
  · exact staging pid

/-- Every original routed transmission carries one paired account through
front admission, selected ownership, concrete creation and final repayment.
This is a local source contract, with an explicit incoming account. -/
theorem transmit (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StatePrefixPreserves (Carrier debts locals) (Safe debts)
      (Driver.transmitObserved hooks family addr packets mtu) := by
  unfold Driver.transmitObserved
  apply StatePrefixEnsures.bind (CompleteFront.checked ⟨family,addr,packets,mtu⟩ (Safe debts)
    (fun ledger => Safe.accounted ledger locals))
  intro result
  cases result with
  | error err => exact pure_accounted err
  | ok pid =>
    exact StatePrefixEnsures.bind (staging pid) (fun _ =>
      StatePrefixEnsures.bind (CompleteSource.original (some pid) (Safe debts)
        (fun ledger => Safe.accounted ledger locals)) (fun _ => pure_accounted 0))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteTransmit
