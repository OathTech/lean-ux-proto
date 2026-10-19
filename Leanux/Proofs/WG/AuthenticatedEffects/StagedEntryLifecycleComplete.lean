import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntrySendDrain

/-! Removal and shutdown use the actual bounded drain, with all its send and
clear callbacks discharged. These contracts keep the debt and local-owner
indices fixed and retain the accounted history on native failure. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.LifecycleComplete
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal HandshakeSecurity SourcePassive Driver

variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (entrySafe : ∀ ledger h w, Inv h ledger debts locals w → Safe h)
include entrySafe

theorem timers_stop (pid : PeerId) : Checked debts locals Safe
    (SendExchange.timersStopWith liftWGPrefix (sendDrainObserved hooks) pid) :=
  LifecycleSource.timers_stop Safe entrySafe (SendDrain.checked Safe entrySafe) pid

theorem after_dead (pid : PeerId) : Checked debts locals Safe
    (StagedDisposal.Lifecycle.afterDeadWith liftWGPrefix (sendDrainObserved hooks) hooks.peerRelease pid) :=
  LifecycleSource.after_dead Safe entrySafe (SendDrain.checked Safe entrySafe) pid

theorem remove (peer : Option PeerId) : Checked debts locals Safe (removeObserved hooks peer) :=
  LifecycleSource.remove Safe entrySafe (SendDrain.checked Safe entrySafe) peer

theorem remove_all : Checked debts locals Safe (removeAllObserved hooks) :=
  LifecycleSource.remove_all Safe entrySafe (SendDrain.checked Safe entrySafe)

theorem down : Checked debts locals Safe (downObserved hooks) :=
  LifecycleSource.down Safe entrySafe (SendDrain.checked Safe entrySafe)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.LifecycleComplete
