import Leanux.Proofs.WG.AuthenticatedEffects.CausalSelectionConfiguration

/-! Actual shutdown and deletion use the same guarded observed send drains.
Native creation/deletion cannot invent selection receipts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Selections.Carrier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do
open Queues Configuration TransmitSecurity.Driver HandshakeSecurity.SendExchange
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

macro "selection_lifecycle_step" : tactic => `(tactic| first
  | (selection_carrier_head liftWGPrefix; apply state_native; solve | causal_delayed_lifecycle_step)
  | selection_removal_step)

theorem down : StateSafe (downObserved hooks) := by
  unfold downObserved
  rw [show hooks.stagedPurge = (fun pid => liftWGPrefix (purgeStagedPackets pid)) from rfl,
    Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.Lifecycle.down_neutral]
  unfold downWith stopWith timersStopWith
  repeat' first
    | (selection_carrier_head sendDrainObserved; exact sendDrain _)
    | selection_lifecycle_step

theorem destruct : StateSafe (destructObserved hooks) := by
  change StateSafe (Configuration.destructWith liftWGPrefix (removeAllObserved hooks) _)
  unfold Configuration.destructWith
  repeat' first
    | (selection_carrier_head removeAllObserved; exact removeAll)
    | selection_lifecycle_step
  exact state_native _ Delayed.destruct_finish

theorem device_create : StateSafe (liftWGPrefix wgCreate) := state_native _ Delayed.device_create

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Selections.Carrier
