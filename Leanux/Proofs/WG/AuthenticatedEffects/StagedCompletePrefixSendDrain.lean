import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixSendWorker
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixClearWorker
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixSendDrainFrames

/-! The original bounded send/clear drain retains every logical prefix.
Its concrete send and clear callbacks select the same successor ledgers as
the original accounting proofs; native interval correspondence is separate. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.SendDrain
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal Driver
open _root_.Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Passive
open CompleteCarrier (Accounted)
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h)
include accountSafe

omit accountSafe in
theorem list {α β : Type} (items : List α) (initial : β)
    (body : α→β→WGPrefix Event (ForInStep β))
    (checked : ∀ item acc, StateEnsures (CompleteCarrier.Carrier debts locals) Safe
      (body item acc) (fun _=>CompleteCarrier.Carrier debts locals)) :
    Checked debts locals Safe (forIn items initial body) :=
  StateEnsures.forIn items initial body (fun _=>CompleteCarrier.Carrier debts locals) checked

theorem with_callbacks (send clear : PeerId → WGPrefix Event Unit)
    (sends : ∀ pid, Checked debts locals Safe (send pid))
    (clears : ∀ pid, Checked debts locals Safe (clear pid)) (upTo : Option PeerId) :
    Checked debts locals Safe (HandshakeSecurity.SendExchange.drainWith liftWGPrefix send clear upTo) := by
  change StateEnsures (CompleteCarrier.Carrier debts locals) Safe _ (fun _ => CompleteCarrier.Carrier debts locals)
  unfold HandshakeSecurity.SendExchange.drainWith
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | (entry_callback_head send; exact sends _)
    | (entry_callback_head clear; exact clears _)
    | (maintenance_head ForIn.forIn; apply list Safe)
    | (maintenance_head liftWGPrefix
       apply Passive.native Safe accountSafe
       intro initial
       change Preserves (fun w => StagedEntry.view w = initial) _
       first
       | (rx_retention_head getDev; exact TimerFrames.store getDev_sameWGStore initial)
       | (rx_retention_head peekUnit; exact hoare_liftAmbient (peekUnit _) _)
       | (rx_retention_head resolveUnit; exact hoare_liftAmbient (resolveUnit _ _ _) _)
       | (rx_retention_head getAmbient; unfold getAmbient; exact hoare_liftAmbient (get : AmbientM Ambient) _)
       | (rx_retention_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
       | (rx_retention_head throw; exact SendDrainFrames.stop _ initial))
    | prefix_handshake_step Safe using accountSafe

theorem checked (upTo : Option PeerId) :
    Checked debts locals Safe (sendDrainObserved hooks upTo) :=
  with_callbacks Safe accountSafe _ _ (Send.flushed Safe accountSafe)
    (Clear.flushed Safe accountSafe) upTo

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.SendDrain
