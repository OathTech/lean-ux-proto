import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntrySendWorkerFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixHandshakeWorker

/-! Logical-prefix extension of the original source contract.
Native silent-interval correspondence remains separate.

 Actual queued sends retain both accounting directions through native
creation, protocol socket, timer receipts and counted peer repayment.
Passive suffixes keep one ledger; repayment uses its exact paired successor. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Send
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open _root_.Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Passive
open CompleteCarrier (Accounted)
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
variable (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h)
include accountSafe

theorem send (pid : PeerId) : Checked debts locals Safe (sendWith ops pid) := by
  change StateEnsures (CompleteCarrier.Carrier debts locals) Safe _ (fun _ => CompleteCarrier.Carrier debts locals)
  unfold sendWith ops
  simp only [SendEffects.withEffects,HandshakeSecurity.ExchangeJoint.sendOps,
    HandshakeSecurity.StagedDisposal.Decoration.send,ProtocolSender.sendOps,SendEffects.native]
  repeat' first
    | (entry_consumer_update_head
       apply Passive.update_bind Safe accountSafe
       · intro p; exact ⟨rfl,rfl,rfl⟩
       intro ignored
       change StateEnsures (CompleteCarrier.Carrier _ _) _ _ (fun _ => CompleteCarrier.Carrier _ _))
    | (maintenance_lift_action_head createInitiation
       exact Passive.native Safe accountSafe _ (SendWorkerFrames.create _))
    | (maintenance_head TimerEffects.initiatedWith
       exact Timer.initiated Safe accountSafe _)
    | prefix_handshake_step Safe using accountSafe

theorem worker (pid : PeerId) : Checked debts locals Safe (workerWith ops pid) :=
  bind_checked Safe (send Safe accountSafe pid)
    (fun _ => Disposal.original (some pid) Safe accountSafe)

theorem after_take (pid : PeerId) : Checked debts locals Safe
    (afterTakeWith liftWGPrefix (workerWith ops) pid) := by
  rw [SendWorkerFrames.after_factor]
  exact bind_checked Safe (Passive.native Safe accountSafe _ (SendWorkerFrames.before_frame pid))
    (fun _ => bind_checked Safe (worker Safe accountSafe pid)
      (fun _ => bind_checked Safe (Passive.native Safe accountSafe _ (TimerFrames.hidden_frame _))
        (fun _ => pure_checked Safe accountSafe ())))

theorem flushed_body (pid : PeerId) : Checked debts locals Safe
    (flushedWith liftWGPrefix (workerWith ops) pid) :=
  bind_checked Safe (Passive.native Safe accountSafe _
      (ReceiveFrames.device _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)))
    (fun _ => after_take Safe accountSafe pid)

theorem flushed (pid : PeerId) : Checked debts locals Safe (CausalJournal.flushedSend pid) := by
  intro w a h entry
  exact Passive.scope Safe accountSafe (.sendWork pid (CausalSources.sendEntry pid w))
    _ (flushed_body Safe accountSafe pid) w a h entry

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Send
