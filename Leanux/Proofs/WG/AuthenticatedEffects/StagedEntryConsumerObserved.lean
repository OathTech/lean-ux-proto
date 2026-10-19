import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryConsumerSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntrySourceEvents

/-! The actual admission and completed-cookie observers retain their native
checking paths, counted repayments and pre-Stop history on the same execution. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.ConsumerObserved
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal SourcePassive
open ConsumerSource NestedPeerRelease
variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (entrySafe : ∀ ledger h w, Inv h ledger debts locals w → Safe h)
include entrySafe

abbrev admission := Event.old ∘ Journal.Event.handshake ∘ HandshakeCausal.Event.admission

theorem initiation (mac : HandshakeMac) : Checked debts locals Safe
    (admitInitiationWith nested admission mac) := by
  unfold admitInitiationWith
  apply bind_checked Safe (StatePrefixPreserves.captureWGObserved (initiation_check Safe entrySafe mac.input))
  intro checked
  dsimp only
  split
  · exact bind_checked Safe (SourceEvents.emit Safe entrySafe _ rfl)
      (fun _ => SourcePassive.native Safe entrySafe _ (ConsumerFrames.initiation_continue _ _))
  · exact SourcePassive.native Safe entrySafe _ (ConsumerFrames.initiation_continue _ _)

theorem response (mac : HandshakeMac) : Checked debts locals Safe
    (admitResponseWith nested admission mac) := by
  unfold admitResponseWith
  apply bind_checked Safe (StatePrefixPreserves.captureWGObserved (response_check Safe entrySafe mac.input))
  intro checked
  dsimp only
  split
  · exact bind_checked Safe (SourceEvents.emit Safe entrySafe _ rfl)
      (fun _ => SourcePassive.native Safe entrySafe _ (ConsumerFrames.response_continue _ _))
  · exact SourcePassive.native Safe entrySafe _ (ConsumerFrames.response_continue _ _)

theorem cookie (msg : Key) : Checked debts locals Safe
    (NestedPeerRelease.cookieObserved nested Event.cookieConsumed msg) :=
  SourceEvents.receipt Safe entrySafe _ _ (ConsumerSource.cookie Safe entrySafe msg) (fun _ => rfl)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.ConsumerObserved
