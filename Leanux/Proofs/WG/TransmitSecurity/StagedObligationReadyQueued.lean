import Leanux.Proofs.WG.TransmitSecurity.StagedObligationReadyStaging
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryQueued

/-! The restored no-key branch uses the actual queued-initiation contract.
Its history suffix and stopped cuts require no incoming funding assumption. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.ReadyCarrier
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes
open Staged.Origins AuthenticatedEffects CausalJournal StagedProvenance RetirementSecurity AllocatedObligation
open HandshakeSecurity.StagedConservation

theorem queued (pid : PeerId) (Safe : List Event → Prop)
    (entrySafe : ∀ h w, StagedEntry.Inv h ledger debts locals w → Safe h)
    (Post : List Event → WGWorld → Ambient → Prop)
    (entryPost : ∀ h w a, StagedEntry.Inv h ledger debts locals w → Post h w a) :
    StatePrefixEnsures (fun h w _ => StagedEntry.Inv h ledger debts locals w) Safe
      (HandshakeSecurity.StagedDisposal.Effects.queuedWith effects peerRelease pid false) (fun _ => Post) := by
  intro w a h before
  have result := StagedEntry.Queued.checked pid before a
  cases performed : runWGPrefix
      (HandshakeSecurity.StagedDisposal.Effects.queuedWith effects peerRelease pid false) w a h with
  | mk outcome last =>
    rw [performed] at result
    change runPrefix ((HandshakeSecurity.StagedDisposal.Effects.queuedWith effects peerRelease pid false).run w) a h = _ at performed
    rw [performed]
    cases outcome with
    | error stop =>
      obtain ⟨same,_⟩ := result
      change last = h at same
      subst last
      exact ⟨[],by simp,entrySafe _ _ before,True.intro⟩
    | ok out =>
      obtain ⟨⟨value,v⟩,b⟩ := out
      cases value
      obtain ⟨entry,trace⟩ := result
      have appended : ∃ suffix, last = h ++ suffix := by
        cases trace with
        | idle _ => exact ⟨[],by simp⟩
        | repaid _ _ => exact ⟨_,rfl⟩
        | queued _ _ => exact ⟨_,rfl⟩
      obtain ⟨suffix,extended⟩ := appended
      exact ⟨suffix,extended,entrySafe _ _ entry,entryPost _ _ _ entry⟩

/-- Every actual staging outcome has an accounted selected frontier or a
complete entry; only the actual data-creation callback remains to be joined. -/
theorem staging_created (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (pid : PeerId) (Safe : List Event → Prop)
    (entrySafe : ∀ ledger h w, StagedEntry.Inv h ledger debts locals w → Safe h)
    (activeSafe : ∀ ledger generation peer position h,
      SoundHeld.Active ledger debts generation pid peer position h → Safe h)
    (Post : List Event → WGWorld → Ambient → Prop) (postSafe : ∀ h w a, Post h w a → Safe h)
    (entryPost : ∀ ledger h w a, StagedEntry.Inv h ledger debts locals w → Post h w a)
    (created : ∀ ledger items, StatePrefixEnsures
      (fun h w _ => StagedEntry.Inv h ledger debts (⟨.unpublished,pid,items⟩ :: locals) w ∧
        CreateDisposal.PendingBatch h ledger items)
      Safe (CausalJournal.create pid items) (fun _ => Post)) :
    StatePrefixEnsures (fun h w _ => StagedEntry.Inv h ledger debts locals w) Safe
      (Driver.stagingObserved hooks pid) (fun _ => Post) :=
  staging ledger debts locals pid Safe entrySafe activeSafe Post postSafe (entryPost ledger)
    (fun ledger => queued pid Safe (entrySafe ledger) Post (entryPost ledger)) created

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.ReadyCarrier
