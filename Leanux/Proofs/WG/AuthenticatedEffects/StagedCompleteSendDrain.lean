import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteSendWorker
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteClearWorker

/-! The native bounded send/clear drain preserves both directions of ticket
accounting. Every actual callback selects one successor ledger, while stopped
continuations retain the enclosing same-ledger accounted witness. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteSendDrain
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal CompletePassive Driver
open CompleteCarrier (Accounted)
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h)
private theorem stop (reason : Stop) : SameView StagedEntry.view (throw reason : WG.M α) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a value v b performed
  cases performed

include accountSafe

theorem list {α β : Type} (items : List α) (initial : β)
    (body : α → β → WGPrefix Event (ForInStep β))
    (checked : ∀ item acc, StatePrefixEnsures (CompleteCarrier.Carrier debts locals) Safe
      (body item acc) (fun _ => CompleteCarrier.Carrier debts locals)) :
    Checked debts locals Safe (forIn items initial body) :=
  StatePrefixEnsures.forInInvariant items initial body (fun _ => CompleteCarrier.Carrier debts locals) Safe
    (fun _ h w _ before => by obtain ⟨ledger,accounted⟩ := before; exact accountSafe ledger h w accounted) checked

theorem with_callbacks (send clear : PeerId → WGPrefix Event Unit)
    (sends : ∀ pid, Checked debts locals Safe (send pid))
    (clears : ∀ pid, Checked debts locals Safe (clear pid)) (upTo : Option PeerId) :
    Checked debts locals Safe (HandshakeSecurity.SendExchange.drainWith liftWGPrefix send clear upTo) := by
  change StatePrefixEnsures (CompleteCarrier.Carrier debts locals) Safe _ (fun _ => CompleteCarrier.Carrier debts locals)
  unfold HandshakeSecurity.SendExchange.drainWith
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | (entry_callback_head send; exact sends _)
    | (entry_callback_head clear; exact clears _)
    | (maintenance_head ForIn.forIn; apply list Safe accountSafe)
    | (maintenance_head liftWGPrefix
       apply CompletePassive.native Safe accountSafe
       intro initial
       change Preserves (fun w => StagedEntry.view w = initial) _
       first
       | (rx_retention_head getDev; exact TimerFrames.store getDev_sameWGStore initial)
       | (rx_retention_head peekUnit; exact hoare_liftAmbient (peekUnit _) _)
       | (rx_retention_head resolveUnit; exact hoare_liftAmbient (resolveUnit _ _ _) _)
       | (rx_retention_head getAmbient; unfold getAmbient; exact hoare_liftAmbient (get : AmbientM Ambient) _)
       | (rx_retention_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
       | (rx_retention_head throw; exact stop _ initial))
    | complete_handshake_step Safe using accountSafe

theorem checked (upTo : Option PeerId) :
    Checked debts locals Safe (sendDrainObserved hooks upTo) :=
  with_callbacks Safe accountSafe _ _ (CompleteSend.flushed Safe accountSafe)
    (CompleteClear.flushed Safe accountSafe) upTo

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteSendDrain
