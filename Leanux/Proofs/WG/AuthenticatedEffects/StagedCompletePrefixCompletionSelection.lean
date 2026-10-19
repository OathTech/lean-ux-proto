import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixCompletionDead
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteTxSelection

/-! Prefix transport follows the actual drop and branch cuts. The packet
batch and selected ledger are those supplied by the native queue removal. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Completion
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch Staged.Obligations StagedTerminalComplete
open HandshakeSecurity.StagedConservation

theorem dispatch (pid : PeerId) (items : List SkbId) (head : DataPacket)
    (before : CompleteCarrier.Accounted history ledger [] (⟨.selected,pid,items⟩ :: locals) w.wg)
    (pending : CreateDisposal.PendingBatch history ledger items)
    (earlier : All CompleteProduct.Safe history) :
    All CompleteProduct.Safe (runPrefix (TxWorker.dispatch pid items head) w history).2 := by
  obtain ⟨u,guarded,same⟩ := TxWorker.guard .txCrypted (head.state == .crypted) w history
  have atGuard : CompleteCarrier.Accounted history ledger [] (⟨.selected,pid,items⟩ :: locals) u.wg := by
    simpa only [same] using before
  unfold TxWorker.dispatch
  rw [runPrefix_bind,guarded]
  simp only []
  split
  · exact (crypted ledger locals pid items head u history global_account_safe atGuard pending earlier).1
  · exact (dead pid items head atGuard pending earlier).1

theorem after_read (pid : PeerId) (items : List SkbId) (head : DataPacket)
    (before : CompleteCarrier.Accounted history ledger [] locals w.wg)
    (cached : ∀ p, peerAt w.wg pid = some p → p.txQueue.peeked = some items)
    (earlier : All CompleteProduct.Safe history) :
    All CompleteProduct.Safe (runPrefix (TxWorker.afterRead pid items head) w history).2 := by
  have paired := Converse.drop_complete pid items before.complete w
  have allDrop := ledger_quiet (CausalJournal.completionOps.drop pid items) (Appends.focus _ _ _)
    (Converse.drop_history pid items) global_account_safe before earlier
  rw [TxWorker.afterRead_factor,runPrefix_bind]
  cases removed : runPrefix (CausalJournal.completionOps.drop pid items) w history with
  | mk outcome middle =>
    rw [removed] at paired allDrop
    cases outcome with
    | error stop => exact allDrop
    | ok out =>
      obtain ⟨ignored,u⟩ := out
      cases ignored
      obtain ⟨entry,pending⟩ := TxSelection.drop_entry pid items before.entry cached removed
      exact dispatch pid items head ⟨entry,paired⟩ pending allDrop

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Completion
