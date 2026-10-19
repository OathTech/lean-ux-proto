import Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrierConfiguration
import Leanux.Proofs.WG.AuthenticatedEffects.TransportLifecycleSourceFrames

/-! Native shutdown and deletion transport the RX carrier through every real
handshake-work drain, including drains nested in timer cancellation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Configuration TransmitSecurity.Driver HandshakeSecurity.SendExchange
set_option maxRecDepth 4096
set_option maxHeartbeats 600000
variable {E : Type} {extra : List E → Prop}
  {origin : E → Option TransportDriver.OriginEvent} {replay : E → Option TransportDriver.Replay}
  {hooks : Hooks E}

macro "transport_lifecycle_rx" : tactic => `(tactic| first
  | (snapshot_head requireNotPending; exact TransportLifecycle.pending_rx _ _)
  | (snapshot_head purgeStagedPackets; exact
      ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationTimers.«0».Leanux.Proofs.WG.PublicationFrontier.purge_geometry) _).factor Prod.snd)
  | (snapshot_head handshakeClear; exact clearHandshake_rx _)
  | (snapshot_head resetLastSentHandshake; exact (TransportLifecycle.reset_geometry _).factor Prod.snd)
  | (snapshot_head socketReinit; exact TransportConfiguration.socket_rx _ (socketReinit_sameSocket _ _))
  | transport_removal_rx)

macro "transport_lifecycle_state_step" : tactic => `(tactic| first
  | (transport_carrier_head liftWGPrefix; solve | apply state_rx; transport_lifecycle_rx)
  | transport_carrier_state_step)

theorem down (effects : EffectsSafe extra origin replay hooks) (flushed : ∀ pid, StateSafe extra origin replay (hooks.flushedSend pid)) :
    StateSafe extra origin replay (downObserved hooks) := by
  unfold downObserved HandshakeSecurity.StagedDisposal.Lifecycle.downWith
    HandshakeSecurity.StagedDisposal.Lifecycle.stopWith timersStopWith
  repeat' first
    | (transport_carrier_head Hooks.stagedPurge; exact effects.stagedPurge _)
    | (transport_carrier_head sendDrainObserved; exact sendDrain flushed _)
    | transport_lifecycle_state_step

theorem destruct (effects : EffectsSafe extra origin replay hooks) (flushed : ∀ pid, StateSafe extra origin replay (hooks.flushedSend pid)) :
    StateSafe extra origin replay (destructObserved hooks) := by
  change StateSafe extra origin replay (Configuration.destructWith liftWGPrefix (removeAllObserved hooks) _)
  unfold Configuration.destructWith
  repeat' first
    | (transport_carrier_head removeAllObserved; exact removeAll effects flushed)
    | transport_lifecycle_state_step
  exact state_native _ TransportLifecycle.finish

end Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrier
