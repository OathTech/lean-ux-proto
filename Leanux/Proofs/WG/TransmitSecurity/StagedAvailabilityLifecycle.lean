import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityConfiguration
import Leanux.Proofs.WG.HandshakeSecurity.StagedAvailableLifecycle

/-! Staged origins follow the actual shutdown and destruction drains. Reference
release may remove queues; every surviving staged selection keeps its origin. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration
open Driver AuthenticatedEffects AuthenticatedEffects.CausalJournal HandshakeSecurity
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem down : StateSafe (downObserved hooks) := by
  unfold downObserved
  rw [show hooks.stagedPurge = (fun pid => liftWGPrefix (purgeStagedPackets pid)) from rfl,
    Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.Lifecycle.down_neutral]
  unfold SendExchange.downWith SendExchange.stopWith requireNotPending
  repeat' first
    | (available_origin_head SendExchange.timersStopWith; exact timers_stop _)
    | available_configuration_step

theorem destruct : StateSafe (destructObserved hooks) := by
  change StateSafe (Configuration.destructWith liftWGPrefix
    (removeAllObserved hooks) (liftWGPrefix Exchange.destructFinishSource))
  unfold Configuration.destructWith
  repeat' first
    | (available_origin_head removeAllObserved; exact remove_all)
    | (available_origin_head Exchange.destructFinishSource; exact state_lift _ (fun _ => Native.destruct_finish))
    | (available_origin_head liftWGPrefix; exact state_lift _ (fun _ => Native.destruct_finish))
    | available_configuration_step

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
