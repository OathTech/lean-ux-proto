import Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrierStaging
import Leanux.Proofs.WG.Packets.PublicationTimers

/-! The real post-authentication consumer and all five native timer paths
retain the packet authentication carrier independently of peer/key cleanup. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity.Driver
set_option maxHeartbeats 600000
variable {E : Type} {extra : List E → Prop} {origin : E → Option TransportDriver.OriginEvent}
  {replay : E → Option TransportDriver.Replay} {hooks : Hooks E}

theorem prepareRest_rx (pid : PeerId) (pkt : RxPacket) :
    SameView RxDisposition.nativeRxStore (RxCredits.prepareRest pid pkt) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a value v b run
  obtain ⟨delta,transfer⟩ := (hoare_iff_run_ambient _ _ _).mp
    (RxCredits.prepareRest_transfer w pid pkt) w a value v b (RxCredits.Transfer.refl w) run
  exact transfer.rx

theorem finish_rx (pid : PeerId) (ready : Packets.RxReady) :
    SameView RxDisposition.nativeRxStore (Packets.rxFinish pid ready) :=
  (RxCredits.rxFinish_protect pid ready).factor (fun p => p.2.1)

theorem endpoint_rx (pid : PeerId) (ep : Endpoint) :
    SameView RxDisposition.nativeRxStore (setPeerEndpoint pid ep) :=
  ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.endpoint_geometry) pid ep).factor Prod.snd

theorem handshakeComplete_rx (pid : PeerId) (site : HiddenSite) :
    SameView RxDisposition.nativeRxStore (timersHandshakeComplete pid site) :=
  ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.handshake_geometry) pid site).factor Prod.snd

theorem timer_rx (pid : PeerId) (timer : PeerTimer) :
    SameView RxDisposition.nativeRxStore (timerCallback pid timer) :=
  ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationTimers.«0».Leanux.Proofs.WG.PublicationFrontier.timerCallback_geometry) pid timer).factor Prod.snd

theorem timer (h : StagingSafe extra origin replay hooks) (pid : PeerId) (t : PeerTimer) :
    StateSafe extra origin replay (timerObserved hooks pid t) := by
  cases t <;> unfold timerObserved
  · exact effects_retransmit h.toEffectsSafe pid
  · exact expired h pid
  · exact effects_expiredNew h.toEffectsSafe pid
  · exact state_rx _ (timer_rx pid .zeroKeyMaterial)
  · exact persistent h pid

theorem finish_nested (h : StagingSafe extra origin replay hooks) (pid : PeerId) (ready : Packets.RxReady) :
    StateSafe extra origin replay (RetirementSecurity.NestedPeerRelease.rxFinishWith (nestedOps hooks) pid ready) := by
  unfold RetirementSecurity.NestedPeerRelease.rxFinishWith RetirementSecurity.NestedPeerRelease.rxAfterLookupWith
  simp only [nestedOps]
  repeat' first
    | (transport_carrier_head Hooks.peerRelease; exact h.peerRelease _)
    | (transport_carrier_head liftWGPrefix; solve
       | transport_carrier_native lookupSrc
         exact state_rx _ (((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.lookup_geometry) _ _).factor Prod.snd))
    | (transport_carrier_head liftWGPrefix; solve | apply state_rx; transport_effect_rx)
    | transport_carrier_state_step

theorem receiveTail (h : StagingSafe extra origin replay hooks) (pid : PeerId) (pkt : RxPacket) (confirmed : Bool) :
    StateSafe extra origin replay (receiveTailObserved hooks pid pkt confirmed) := by
  unfold receiveTailObserved
  repeat' first
    | (transport_carrier_head RetirementSecurity.NestedPeerRelease.rxFinishWith; exact finish_nested h _ _)
    | (transport_carrier_head stagingObserved; exact staging h _)
    | (transport_carrier_head HandshakeSecurity.StagedDisposal.PacketSource.prepareWith; exact effects_prepare h.toEffectsSafe _ _)
    | (transport_carrier_head liftWGPrefix; first
       | solve | transport_carrier_native RxCredits.prepareRest; exact state_rx _ (prepareRest_rx _ _)
       | solve | transport_carrier_native Packets.rxFinish; exact state_rx _ (finish_rx _ _)
       | solve | transport_carrier_native timersHandshakeComplete; exact state_rx _ (handshakeComplete_rx _ _))
    | transport_staging_step

theorem consume (h : StagingSafe extra origin replay hooks)
    (confirmed : ∀ pid kid, StateSafe extra origin replay (hooks.confirmation pid kid))
    (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    StateSafe extra origin replay (consumeObserved hooks pid pkt ep) := by
  unfold consumeObserved
  repeat' first
    | (transport_carrier_head Hooks.confirmation; exact confirmed _ _)
    | (transport_carrier_head receiveTailObserved; exact receiveTail h _ _ _)
    | (transport_carrier_head liftWGPrefix; solve | transport_carrier_native setPeerEndpoint; exact state_rx _ (endpoint_rx _ _))
    | transport_staging_step

end Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrier
