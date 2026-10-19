import Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrierTraffic
import Leanux.Proofs.WG.AuthenticatedEffects.TransportConfigurationFrames

/-! RX authentication carriers through actual selected and removal-flushed
handshake work. The supplied callback contract applies at every real drain. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Configuration TransmitSecurity.Driver HandshakeSecurity.SendExchange
set_option maxRecDepth 4096
set_option maxHeartbeats 600000
variable {E : Type} {extra : List E → Prop}
  {origin : E → Option TransportDriver.OriginEvent} {replay : E → Option TransportDriver.Replay}
  {hooks : Hooks E}

private theorem removal_ambient_rx (action : AmbientM α) :
    SameView RxDisposition.nativeRxStore (MonadLift.monadLift action : WG.M α) :=
  fun initial => hoare_liftAmbient action (fun w => RxDisposition.nativeRxStore w = initial)

private theorem removal_throw_rx (err : Stop) :
    SameView RxDisposition.nativeRxStore (throw err : WG.M α) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a x v b run
  cases run

macro "transport_removal_rx" : tactic => `(tactic| first
  | (snapshot_head runFlushedClearWork; exact flushedClear_rx _)
  | (snapshot_head keypairsClear; exact clearKeys_rx _)
  | (snapshot_head delTimer; exact delTimer_rx _ _)
  | (snapshot_head timersStop; exact (TransportRemoval.timersStop_geometry _).factor Prod.snd)
  | (snapshot_head peerMakeDead; exact (TransportRemoval.dead_geometry _).factor Prod.snd)
  | (snapshot_head free; exact
      (pinned_const _private.Leanux.Proofs.WG.Packets.PublicationRemoval.«0».Leanux.Proofs.WG.PublicationFrontier.allowedipsFree_geometry).factor Prod.snd)
  | (snapshot_head modifyDev; apply modifyDev_rx <;> intro d <;> rfl)
  | (first | snapshot_head peekUnit | snapshot_head resolveUnit | snapshot_head getAmbient
           | snapshot_head throw | snapshot_head invariant | snapshot_head unsupported
     exact removal_ambient_rx _)
  | transport_native_rx)

macro "transport_removal_step" : tactic => `(tactic| first
  | (transport_carrier_head liftWGPrefix; solve | apply state_rx; transport_removal_rx)
  | transport_carrier_state_step)

theorem sendDrain (flushed : ∀ pid, StateSafe extra origin replay (hooks.flushedSend pid))
    (upTo : Option PeerId) : StateSafe extra origin replay (sendDrainObserved hooks upTo) := by
  unfold sendDrainObserved drainWith
  repeat' first
    | (transport_carrier_head Hooks.flushedSend; exact flushed _)
    | transport_removal_step
  all_goals exact state_rx _ (removal_throw_rx _)

theorem removeAfter (flushed : ∀ pid, StateSafe extra origin replay (hooks.flushedSend pid))
    (pid : PeerId) : StateSafe extra origin replay
      (afterDeadWith liftWGPrefix (sendDrainObserved hooks) pid) := by
  unfold afterDeadWith timersStopWith
  repeat' first
    | (transport_carrier_head sendDrainObserved; exact sendDrain flushed _)
    | transport_removal_step

theorem remove (flushed : ∀ pid, StateSafe extra origin replay (hooks.flushedSend pid))
    (peer : Option PeerId) : StateSafe extra origin replay (removeObserved hooks peer) := by
  unfold removeObserved removeWith peerRemoveWith
  repeat' first
    | (transport_carrier_head afterDeadWith; exact removeAfter flushed _)
    | transport_removal_step
  all_goals simp_all only [Option.some.injEq]
  all_goals first | exact removeAfter flushed _ | contradiction

theorem removeAll (flushed : ∀ pid, StateSafe extra origin replay (hooks.flushedSend pid)) :
    StateSafe extra origin replay (removeAllObserved hooks) := by
  unfold removeAllObserved removeAllWith peerRemoveAllWith
  repeat' first
    | (transport_carrier_head afterDeadWith; exact removeAfter flushed _)
    | transport_removal_step
  all_goals exact state_rx _ ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationRemoval.«0».Leanux.Proofs.WG.PublicationFrontier.allowedipsFree_geometry).factor Prod.snd)

end Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrier
