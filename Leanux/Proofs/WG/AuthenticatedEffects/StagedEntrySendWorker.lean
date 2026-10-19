import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntrySendWorkerFrames

/-! Actual queued initiation sends retain entry accounting through creation,
socket return, timer effects and the counted repayment. The enclosing lexical
scope observes the same dequeued work; it does not grant authorization. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.SendWorker
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal SourcePassive
open HandshakeSecurity.SendExchange
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

def ops : Ops (WGPrefix Event) :=
  SendEffects.withEffects
    (HandshakeSecurity.ExchangeJoint.sendOps Event.exchange
      (HandshakeSecurity.StagedDisposal.Decoration.send Event.stagedDisposal stagedDisposal?
        (ProtocolSender.sendOps Event.protocolSocket scope?))) effects

variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (entrySafe : ∀ ledger h w, Inv h ledger debts locals w → Safe h)
include entrySafe

theorem send (pid : PeerId) : Checked debts locals Safe (sendWith ops pid) := by
  change StatePrefixEnsures (Source.Carrier debts locals) Safe _ (fun _ => Source.Carrier debts locals)
  unfold sendWith ops
  simp only [SendEffects.withEffects,HandshakeSecurity.ExchangeJoint.sendOps,
    HandshakeSecurity.StagedDisposal.Decoration.send,ProtocolSender.sendOps,SendEffects.native]
  repeat' first
    | (entry_consumer_update_head
       apply TimerQueue.update_bind Safe entrySafe
       · intro p; exact ⟨rfl,rfl,rfl⟩
       intro ignored
       change StatePrefixEnsures (Source.Carrier _ _) _ _ (fun _ => Source.Carrier _ _))
    | (maintenance_lift_action_head createInitiation
       exact SourcePassive.native Safe entrySafe _ (SendWorkerFrames.create _))
    | (maintenance_head TimerEffects.initiatedWith
       exact fixed Safe entrySafe (fun _ => TimerObserved.initiated _))
    | entry_handshake_step Safe using entrySafe

theorem worker (pid : PeerId) : Checked debts locals Safe (workerWith ops pid) :=
  bind_checked Safe (send Safe entrySafe pid)
    (fun _ => Source.release (some pid) Safe entrySafe)

theorem after_take (pid : PeerId) : Checked debts locals Safe
    (afterTakeWith liftWGPrefix (workerWith ops) pid) := by
  rw [SendWorkerFrames.after_factor]
  exact bind_checked Safe (SourcePassive.native Safe entrySafe _ (SendWorkerFrames.before_frame pid))
    (fun _ => bind_checked Safe (worker Safe entrySafe pid)
      (fun _ => bind_checked Safe (SourcePassive.native Safe entrySafe _ (TimerFrames.hidden_frame _))
        (fun _ => pure_checked Safe entrySafe ())))

theorem flushed_body (pid : PeerId) : Checked debts locals Safe
    (flushedWith liftWGPrefix (workerWith ops) pid) :=
  bind_checked Safe (SourcePassive.native Safe entrySafe _
      (ReceiveFrames.device _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)))
    (fun _ => after_take Safe entrySafe pid)

theorem flushed (pid : PeerId) : Checked debts locals Safe (CausalJournal.flushedSend pid) := by
  intro w a h entry
  exact SourceEvents.scope Safe entrySafe (.sendWork pid (CausalSources.sendEntry pid w))
    _ (flushed_body Safe entrySafe pid) w a h entry

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.SendWorker
