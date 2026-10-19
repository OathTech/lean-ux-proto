import Leanux.Proofs.WG.TransmitSecurity.StagedRemovalFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedTraffic

/-! Actual removal carries staged origins through every native send and clear drain. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration
open Driver AuthenticatedEffects AuthenticatedEffects.CausalJournal HandshakeSecurity
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem state_range (range : Std.Legacy.Range) (initial : β)
    (body : Nat → β → WGPrefix Event (ForInStep β))
    (safe : ∀ n acc, StateSafe (body n acc)) : StateSafe (forIn range initial body) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact state_forIn _ initial body safe

macro "staged_configuration_step" : tactic => `(tactic| first
  | (staged_origin_head Hooks.peerRelease; change StateSafe (liftWGPrefix _); apply state_lift; intro history; repeat' staged_configuration_native; done)
  | (staged_origin_head liftWGPrefix; apply state_lift; intro history; repeat' staged_configuration_native; done)
  | (staged_origin_head ForIn.forIn; first | apply state_range | apply state_forIn)
  | staged_origin_step)

theorem send_drain (upTo : Option PeerId) : StateSafe (sendDrainObserved hooks upTo) := by
  unfold sendDrainObserved SendExchange.drainWith
  repeat' first
    | (staged_origin_head Hooks.flushedSend; exact flushed_send_observed _)
    | staged_configuration_step

theorem timers_stop (pid : PeerId) :
    StateSafe (SendExchange.timersStopWith liftWGPrefix (sendDrainObserved hooks) pid) := by
  unfold SendExchange.timersStopWith
  repeat' first
    | (staged_origin_head sendDrainObserved; exact send_drain _)
    | staged_configuration_step

theorem after_dead (pid : PeerId) :
    StateSafe (SendExchange.afterDeadWith liftWGPrefix (sendDrainObserved hooks) pid) := by
  unfold SendExchange.afterDeadWith
  repeat' first
    | (staged_origin_head SendExchange.timersStopWith; exact timers_stop _)
    | (staged_origin_head sendDrainObserved; exact send_drain _)
    | staged_configuration_step

theorem remove_peer (peer : Option PeerId) : StateSafe (removeObserved hooks peer) := by
  unfold removeObserved
  rw [show hooks.peerRelease = (fun peer => liftWGPrefix (peerPut peer)) from rfl,
    Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.Lifecycle.remove_neutral]
  unfold SendExchange.removeWith Configuration.peerRemoveWith
  repeat' first
    | (staged_origin_head SendExchange.afterDeadWith; exact after_dead _)
    | staged_configuration_step

theorem remove_all : StateSafe (removeAllObserved hooks) := by
  unfold removeAllObserved
  rw [show hooks.peerRelease = (fun peer => liftWGPrefix (peerPut peer)) from rfl,
    Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.Lifecycle.removeAll_neutral]
  unfold SendExchange.removeAllWith Configuration.peerRemoveAllWith
  repeat' first
    | (staged_origin_head SendExchange.afterDeadWith; exact after_dead _)
    | staged_configuration_step

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
