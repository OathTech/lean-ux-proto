import Leanux.Proofs.WG.Noise.PendingInvariantFrames
import Leanux.Proofs.WG.Noise.PendingTicketConsumeSource
import Leanux.Proofs.WG.Noise.PendingTicketConsumeClaims
import Leanux.Proofs.WG.Origins.ConfiguredTraffic
import Leanux.Proofs.WG.Origins.ConfiguredReceiveLeaves

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingSession
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues ConfiguredRemoval ConfiguredTraffic

private theorem confirmation_configured (pid : PeerId) (kid : KeypairId) :
    Preserves ConfiguredIdentity.Inv (receivedWithKeypair pid kid) := by
  unfold receivedWithKeypair
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  simp (config := {zeta := false}) only [branch]
  repeat' configured_traffic_step

private theorem freshRx_configured (pid : PeerId) :
    Preserves ConfiguredIdentity.Inv (keepKeyFreshRx pid) := by
  unfold keepKeyFreshRx WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head sendQueuedHandshakeInitiation; exact ConfiguredTraffic.queued _ _)
    | configured_traffic_step

private theorem stats_configured (pid : PeerId) (len : Nat) :
    Preserves ConfiguredIdentity.Inv (updateRxStats pid len) := by
  unfold updateRxStats
  repeat' configured_traffic_step

private theorem dishonest_configured (why : Dishonest) :
    Preserves ConfiguredIdentity.Inv (dishonest why) := by
  cases why <;> unfold dishonest <;> repeat' configured_traffic_step

private def configuredOfBorrow (s : WGStoreView × (PeerId → Option Peer)) :
    Option ConfiguredIdentity.State :=
  s.1.dev.map fun d => ⟨d.ifindex,d.nextPeer,d.peerHashtable,fun pid =>
    (s.2 pid).map ConfiguredIdentity.cell⟩

private theorem configured_borrow_factor (w : WGWorld) :
    ConfiguredIdentity.view w = configuredOfBorrow (PeerBorrow.view w) := by
  cases device : w.dev <;>
    simp [ConfiguredIdentity.view,ConfiguredIdentity.state,configuredOfBorrow,PeerBorrow.view,
      PeerBorrow.outsidePeers,PeerBorrow.resident,wgStoreView,device]

private theorem prepareRest_configured (pid : PeerId) (pkt : RxPacket) :
    Preserves ConfiguredIdentity.Inv (RxCredits.prepareRest pid pkt) := by
  unfold RxCredits.prepareRest WG.andM WG.orM
  material_lower
  repeat' first
    | (rx_retention_head keepKeyFreshRx; exact freshRx_configured _)
    | (rx_retention_head timersAnyAuthenticatedPacketReceived; exact frame
        (ConfiguredReceiveLeaves.timersAnyAuthenticatedPacketReceived_view _))
    | (rx_retention_head timersTraversal; exact frame (ConfiguredIdentity.timersTraversal_view _))
    | (rx_retention_head timersDataReceived; exact frame (ConfiguredReceiveLeaves.timersDataReceived_view _))
    | (rx_retention_head updateRxStats; exact stats_configured _ _)
    | (rx_retention_head dishonest; exact dishonest_configured _)
    | (rx_retention_head inetEcnDecapsulate; exact frame
        (ConfiguredIdentity.sameWG (project := id) (inetEcnDecapsulate_sameWGStore _ _ _)))
    | configured_traffic_step

private theorem rxFinish_configured (pid : PeerId) (ready : Packets.RxReady) :
    Preserves ConfiguredIdentity.Inv (Packets.rxFinish pid ready) := by
  rw [← RxCredits.rxFinishSource_eq]
  unfold RxCredits.rxFinishSource
  material_lower
  repeat' first
    | (rx_retention_head RxBorrow.source; exact frame
        ((RxBorrow.source_frame _ _).of_factor configuredOfBorrow
          ConfiguredIdentity.view configured_borrow_factor))
    | (rx_retention_head updateRxStats; exact stats_configured _ _)
    | (rx_retention_head dishonest; exact dishonest_configured _)
    | configured_traffic_step

theorem consume_configured (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    Preserves ConfiguredIdentity.Inv (consumeDataDone pid pkt endpoint) := by
  rw [ConsumeConfirmation.source]
  unfold ConsumeConfirmation.afterConfirmation
  material_lower
  repeat' first
    | (rx_retention_head setPeerEndpoint; exact frame (ConfiguredReceiveLeaves.setPeerEndpoint_view _ _))
    | (rx_retention_head receivedWithKeypair; exact confirmation_configured _ _)
    | (rx_retention_head timersHandshakeComplete; exact frame
        (ConfiguredReceiveLeaves.timersHandshakeComplete_view _ _))
    | (rx_retention_head sendStagedPackets; exact ConfiguredTraffic.staged _)
    | (rx_retention_head RxCredits.prepareRest; exact prepareRest_configured _ _)
    | (rx_retention_head Packets.rxFinish; exact rxFinish_configured _ _)
    | configured_traffic_step

theorem consume_core (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    Ensures (consumeDataDone pid pkt endpoint)
      (fun w => ConfiguredIdentity.Inv w ∧ CurrentSlots.Inv w)
      (fun _ w => ConfiguredIdentity.Inv w ∧ CurrentSlots.Inv w) := by
  intro w a result v b hi run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (consume_configured pid pkt endpoint)
      w a result v b hi.1 run,
    (hoare_iff_run_ambient _ _ _).mp (CurrentSlots.consumeDataDone_preserves pid pkt endpoint)
      w a result v b hi.2 run⟩

end Leanux.Proofs.WG.Noise.PendingSession
