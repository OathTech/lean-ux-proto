import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryHandshakeWorker

/-! Native clear-worker maintenance uses the same counted peer-release observer
as the shared driver, including direct drains and stopped section boundaries. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.ClearWorker
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal SourcePassive
variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (entrySafe : ∀ ledger h w, Inv h ledger debts locals w → Safe h)
include entrySafe

theorem clear (pid : PeerId) : Checked debts locals Safe
    (NestedPeerRelease.clearWith (Driver.nestedOps hooks) pid) :=
  bind_checked Safe (SourcePassive.native Safe entrySafe _ (KeyFrames.clear pid))
    (fun _ => bind_checked Safe (SourcePassive.native Safe entrySafe _ (KeyFrames.clear_keys pid))
      (fun _ => Source.release (some pid) Safe entrySafe))

theorem flushed (pid : PeerId) : Checked debts locals Safe
    (NestedPeerRelease.flushedClearWith (Driver.nestedOps hooks) pid) := by
  change StatePrefixEnsures (Source.Carrier debts locals) Safe _ (fun _ => Source.Carrier debts locals)
  unfold NestedPeerRelease.flushedClearWith
  simp only [Driver.nestedOps]
  repeat' first
    | (maintenance_head NestedPeerRelease.clearWith; exact clear Safe entrySafe _)
    | entry_handshake_step Safe using entrySafe

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.ClearWorker
