import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverCallers

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Queues.RxCredits Origins Origins.Retaining ConfiguredTraffic

theorem carrier_endpoint (pid : PeerId) (ep : Endpoint) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (setPeerEndpoint pid ep) :=
  carrier_frame confirmed (ConfiguredReceiveLeaves.setPeerEndpoint_view pid ep)
    (native_fields (pool_of_material (setPeerEndpoint_material pid ep))
      ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotCompletion.«0».Leanux.Proofs.WG.CurrentSlots.endpoint_fields) pid ep) confirmed)

theorem carrier_complete (pid : PeerId) (site : HiddenSite) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (timersHandshakeComplete pid site) :=
  carrier_frame confirmed (ConfiguredReceiveLeaves.timersHandshakeComplete_view pid site)
    (native_join (authorization_of_frames (pool_of_material (timersHandshakeComplete_material pid site))
      (control_keyEffects (project := id) (allowed := NoPromotion) (timersHandshakeComplete_control pid site)) confirmed)
      (CurrentSlots.timersHandshakeComplete_preserves pid site))

private theorem prepare_configured (pid : PeerId) (pkt : RxPacket) :
    Framing.Preserves ConfiguredIdentity.Inv (prepareRest pid pkt) := by
  unfold prepareRest keepKeyFreshRx WG.andM WG.orM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head sendQueuedHandshakeInitiation; exact ConfiguredTraffic.queued _ _)
    | (rx_retention_head timersAnyAuthenticatedPacketReceived
       exact ConfiguredRemoval.frame (ConfiguredReceiveLeaves.timersAnyAuthenticatedPacketReceived_view _))
    | (rx_retention_head timersTraversal
       exact ConfiguredRemoval.frame (ConfiguredIdentity.timersTraversal_view _))
    | (rx_retention_head timersDataReceived
       exact ConfiguredRemoval.frame (ConfiguredReceiveLeaves.timersDataReceived_view _))
    | (rx_retention_head updateRxStats
       exact ConfiguredRemoval.frame ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentRx.«0».Leanux.Proofs.WG.CurrentRx.updateRxStats_view) _ _))
    | (rx_retention_head dishonest
       exact ConfiguredRemoval.frame ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentRx.«0».Leanux.Proofs.WG.CurrentRx.dishonest_view) _))
    | (rx_retention_head inetEcnDecapsulate
       exact ConfiguredRemoval.frame (ConfiguredIdentity.sameWG (project := id) (inetEcnDecapsulate_sameWGStore _ _ _)))
    | configured_traffic_step

private theorem prepare_slots (pid : PeerId) (pkt : RxPacket) :
    Framing.Preserves CurrentSlots.Inv (prepareRest pid pkt) := by
  unfold prepareRest WG.andM WG.orM timersAnyAuthenticatedPacketReceived
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head keepKeyFreshRx; exact CurrentSlots.keepKeyFreshRx_preserves _)
    | (rx_retention_head delTimer; exact CurrentSlots.delTimer_preserves _ _)
    | (rx_retention_head timersTraversal; exact CurrentSlots.timersTraversal_preserves _)
    | (rx_retention_head timersDataReceived; exact CurrentSlots.timersDataReceived_preserves _)
    | (rx_retention_head updateRxStats
       exact CurrentSlots.fields_preserves (project := id) ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotCompletion.«0».Leanux.Proofs.WG.CurrentSlots.stats_fields) _ _))
    | (rx_retention_head dishonest
       exact (pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotCompletion.«0».Leanux.Proofs.WG.CurrentSlots.dishonest_preserves) _)
    | (rx_retention_head inetEcnDecapsulate
       exact CurrentSlots.fields_preserves (project := id) ((inetEcnDecapsulate_sameWGStore _ _ _).of_factor
         (fun s : WGStoreView => CurrentSlots.fields {dev := s.dev}) CurrentSlots.fields (fun _ => rfl)))
    | slot_traffic_step

theorem carrier_prepare (pid : PeerId) (pkt : RxPacket) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (prepareRest pid pkt) :=
  carrier_join confirmed (prepare_configured pid pkt)
    (native_join (authorization_of_frames (prepareRest_core pid pkt)
      (prepareRest_keyEffect (allowed := NoPromotion) pid pkt) confirmed) (prepare_slots pid pkt))

private theorem finish_configured (pid : PeerId) (ready : Packets.RxReady) :
    Framing.Preserves ConfiguredIdentity.Inv (Packets.rxFinish pid ready) := by
  unfold Packets.rxFinish Packets.rxAfterLookup
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head lookupSrc
       exact ConfiguredRemoval.frame ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentRx.«0».Leanux.Proofs.WG.CurrentRx.lookupSrc_view) _ _))
    | (rx_retention_head updateRxStats
       exact ConfiguredRemoval.frame ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentRx.«0».Leanux.Proofs.WG.CurrentRx.updateRxStats_view) _ _))
    | (rx_retention_head dishonest
       exact ConfiguredRemoval.frame ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentRx.«0».Leanux.Proofs.WG.CurrentRx.dishonest_view) _))
    | configured_traffic_step

private theorem finish_slots (pid : PeerId) (ready : Packets.RxReady) :
    Framing.Preserves CurrentSlots.Inv (Packets.rxFinish pid ready) := by
  unfold Packets.rxFinish Packets.rxAfterLookup
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head lookupSrc
       exact CurrentSlots.view_preserves (project := id) ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotCompletion.«0».Leanux.Proofs.WG.CurrentSlots.lookupSrc_view) _ _))
    | (rx_retention_head updateRxStats
       exact CurrentSlots.fields_preserves (project := id) ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotCompletion.«0».Leanux.Proofs.WG.CurrentSlots.stats_fields) _ _))
    | (rx_retention_head dishonest
       exact (pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotCompletion.«0».Leanux.Proofs.WG.CurrentSlots.dishonest_preserves) _)
    | slot_traffic_step

theorem carrier_finish (pid : PeerId) (ready : Packets.RxReady) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (Packets.rxFinish pid ready) :=
  carrier_join confirmed (finish_configured pid ready)
    (native_join (authorization_of_frames (rxFinish_core pid ready)
      (keyEffects_view (project := id) (allowed := NoPromotion) (rxFinish_keyView pid ready)) confirmed)
      (finish_slots pid ready))

end Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
