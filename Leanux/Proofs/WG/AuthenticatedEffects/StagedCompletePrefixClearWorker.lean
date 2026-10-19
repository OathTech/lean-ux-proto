import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixHandshakeWorker

/-! Logical-prefix extension of the original source contract.
Native silent-interval correspondence remains separate.

 Clear work retains complete paired accounting through native key clearing
and the actual counted repayment, including direct flushed execution. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Clear
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open _root_.Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Passive
open CompleteCarrier (Accounted)
variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h)
include accountSafe

theorem clear (pid : PeerId) : Checked debts locals Safe
    (NestedPeerRelease.clearWith (Driver.nestedOps hooks) pid) :=
  bind_checked Safe (Passive.native Safe accountSafe _ (KeyFrames.clear pid))
    (fun _ => bind_checked Safe (Passive.native Safe accountSafe _ (KeyFrames.clear_keys pid))
      (fun _ => Disposal.original (some pid) Safe accountSafe))

theorem flushed (pid : PeerId) : Checked debts locals Safe
    (NestedPeerRelease.flushedClearWith (Driver.nestedOps hooks) pid) := by
  change StateEnsures (CompleteCarrier.Carrier debts locals) Safe _ (fun _ => CompleteCarrier.Carrier debts locals)
  unfold NestedPeerRelease.flushedClearWith
  simp only [Driver.nestedOps]
  repeat' first
    | (maintenance_head NestedPeerRelease.clearWith; exact clear Safe accountSafe _)
    | prefix_handshake_step Safe using accountSafe

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Clear
