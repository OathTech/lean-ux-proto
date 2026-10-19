import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntrySendWorker
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryClearWorker
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryLifecycleSource

/-! The actual bounded drain invokes the proved send and clear callbacks at
the native selected work occurrence. Counted releases may settle the ledger;
a stopped drain retains the enclosing accounted-history condition. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.SendDrain
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal SourcePassive Driver
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (entrySafe : ∀ ledger h w, Inv h ledger debts locals w → Safe h)
private theorem stop (reason : Stop) : SameView StagedEntry.view (throw reason : WG.M α) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a value v b performed
  cases performed

include entrySafe

theorem with_callbacks (send clear : PeerId → WGPrefix Event Unit)
    (sends : ∀ pid, Checked debts locals Safe (send pid))
    (clears : ∀ pid, Checked debts locals Safe (clear pid)) (upTo : Option PeerId) :
    Checked debts locals Safe (HandshakeSecurity.SendExchange.drainWith liftWGPrefix send clear upTo) := by
  change StatePrefixEnsures (Source.Carrier debts locals) Safe _ (fun _ => Source.Carrier debts locals)
  unfold HandshakeSecurity.SendExchange.drainWith
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | (entry_callback_head send; exact sends _)
    | (entry_callback_head clear; exact clears _)
    | (maintenance_head ForIn.forIn; apply LifecycleSource.list Safe entrySafe)
    | (maintenance_head liftWGPrefix
       apply SourcePassive.native Safe entrySafe
       intro initial
       change Preserves (fun w => StagedEntry.view w = initial) _
       first
       | (rx_retention_head getDev; exact TimerFrames.store getDev_sameWGStore initial)
       | (rx_retention_head peekUnit; exact hoare_liftAmbient (peekUnit _) _)
       | (rx_retention_head resolveUnit; exact hoare_liftAmbient (resolveUnit _ _ _) _)
       | (rx_retention_head getAmbient; unfold getAmbient; exact hoare_liftAmbient (get : AmbientM Ambient) _)
       | (rx_retention_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
       | (rx_retention_head throw; exact stop _ initial))
    | entry_handshake_step Safe using entrySafe

theorem checked (upTo : Option PeerId) :
    Checked debts locals Safe (sendDrainObserved hooks upTo) :=
  with_callbacks Safe entrySafe _ _ (SendWorker.flushed Safe entrySafe)
    (ClearWorker.flushed Safe entrySafe) upTo

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.SendDrain
