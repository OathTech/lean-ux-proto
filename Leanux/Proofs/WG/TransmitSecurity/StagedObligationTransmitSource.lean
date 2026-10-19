import Leanux.Proofs.WG.TransmitSecurity.StagedObligationReadyQueued
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntrySourceContracts

/-! Full entry transport through the actual transmit/keepalive composition.
Staging's one remaining source callback is creation; routing and queued
initiation use their complete local source contracts. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.EntrySource
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes
open Staged.Origins AuthenticatedEffects CausalJournal StagedProvenance RetirementSecurity AllocatedObligation
open StagedEntry.Source

theorem staging (pid : PeerId) (Safe : List Event → Prop)
    (entrySafe : ∀ ledger h w, StagedEntry.Inv h ledger debts locals w → Safe h)
    (activeSafe : ∀ ledger generation peer position h,
      SoundHeld.Active ledger debts generation pid peer position h → Safe h)
    (created : ∀ ledger items, StatePrefixEnsures
      (fun h w _ => StagedEntry.Inv h ledger debts (⟨.unpublished,pid,items⟩ :: locals) w ∧
        CreateDisposal.PendingBatch h ledger items)
      Safe (CausalJournal.create pid items) (fun _ => Carrier debts locals)) :
    StatePrefixPreserves (Carrier debts locals) Safe (Driver.stagingObserved hooks pid) := by
  intro w a h before
  obtain ⟨ledger,entry⟩ := before
  exact ReadyCarrier.staging_created ledger debts locals pid Safe entrySafe activeSafe
    (Carrier debts locals) (fun h w _ after => after.elim (fun _ => entrySafe _ h w))
    (fun ledger _ _ _ inv => ⟨ledger,inv⟩) created w a h entry

theorem pure_entry (value : α) (Safe : List Event → Prop)
    (entrySafe : ∀ ledger h w, StagedEntry.Inv h ledger debts locals w → Safe h) :
    StatePrefixPreserves (Carrier debts locals) Safe (pure value) :=
  StatePrefixEnsures.pure value (fun h w _ before => before.elim (fun _ => entrySafe _ h w))
    (fun _ _ _ before => before)

theorem keepalive (pid : PeerId) (Safe : List Event → Prop)
    (entrySafe : ∀ ledger h w, StagedEntry.Inv h ledger debts locals w → Safe h)
    (staged : StatePrefixPreserves (Carrier debts locals) Safe (Driver.stagingObserved hooks pid)) :
    StatePrefixPreserves (Carrier debts locals) Safe (Driver.keepaliveObserved hooks pid) := by
  unfold Driver.keepaliveObserved
  apply StatePrefixEnsures.bind (StagedEntry.Source.keepalive pid Safe entrySafe)
  intro ready
  cases ready
  · exact pure_entry () Safe entrySafe
  · exact staged

theorem transmit (family addr : Nat) (packets : List Packet) (mtu : Nat) (Safe : List Event → Prop)
    (entrySafe : ∀ ledger h w, StagedEntry.Inv h ledger debts locals w → Safe h)
    (staged : ∀ pid, StatePrefixPreserves (Carrier debts locals) Safe (Driver.stagingObserved hooks pid)) :
    StatePrefixPreserves (Carrier debts locals) Safe (Driver.transmitObserved hooks family addr packets mtu) := by
  unfold Driver.transmitObserved
  apply StatePrefixEnsures.bind (StagedEntry.Source.front ⟨family,addr,packets,mtu⟩ Safe entrySafe)
  intro result
  cases result with
  | error err => exact pure_entry err Safe entrySafe
  | ok pid =>
    exact StatePrefixEnsures.bind (staged pid) (fun _ =>
      StatePrefixEnsures.bind (StagedEntry.Source.release (some pid) Safe entrySafe)
        (fun _ => pure_entry 0 Safe entrySafe))

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.EntrySource
