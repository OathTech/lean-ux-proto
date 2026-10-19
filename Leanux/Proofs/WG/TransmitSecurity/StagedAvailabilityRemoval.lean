import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityRemovalFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityTraffic

/-! Actual removal carries available staged births through every native send and clear drain. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration
open Driver AuthenticatedEffects AuthenticatedEffects.CausalJournal HandshakeSecurity
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem state_range (range : Std.Legacy.Range) (initial : β)
    (body : Nat → β → WGPrefix Event (ForInStep β))
    (safe : ∀ n acc, StateSafe (body n acc)) : StateSafe (forIn range initial body) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact state_forIn _ initial body safe

macro "available_configuration_step" : tactic => `(tactic| first
  | (available_origin_head liftWGPrefix; apply state_lift; intro history; repeat' available_configuration_native; done)
  | (available_origin_head ForIn.forIn; first | apply state_range | apply state_forIn)
  | available_origin_step)

theorem send_drain (upTo : Option PeerId) : StateSafe (sendDrainObserved hooks upTo) := by
  unfold sendDrainObserved SendExchange.drainWith
  repeat' first
    | (available_origin_head Hooks.flushedSend; exact flushed_send_observed _)
    | available_configuration_step

theorem timers_stop (pid : PeerId) :
    StateSafe (SendExchange.timersStopWith liftWGPrefix (sendDrainObserved hooks) pid) := by
  unfold SendExchange.timersStopWith
  repeat' first
    | (available_origin_head sendDrainObserved; exact send_drain _)
    | available_configuration_step

theorem after_dead (pid : PeerId) :
    StateSafe (SendExchange.afterDeadWith liftWGPrefix (sendDrainObserved hooks) pid) := by
  unfold SendExchange.afterDeadWith
  repeat' first
    | (available_origin_head SendExchange.timersStopWith; exact timers_stop _)
    | (available_origin_head sendDrainObserved; exact send_drain _)
    | available_configuration_step

theorem remove_peer (peer : Option PeerId) : StateSafe (removeObserved hooks peer) := by
  unfold removeObserved SendExchange.removeWith Configuration.peerRemoveWith
  repeat' first
    | (available_origin_head SendExchange.afterDeadWith; exact after_dead _)
    | available_configuration_step

theorem remove_all : StateSafe (removeAllObserved hooks) := by
  unfold removeAllObserved SendExchange.removeAllWith Configuration.peerRemoveAllWith
  repeat' first
    | (available_origin_head SendExchange.afterDeadWith; exact after_dead _)
    | available_configuration_step

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
