import Leanux.Proofs.WG.TransmitSecurity.PacketOriginWorkerFrames
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceHandshakeReceive

/-! Native handshake and cookie frames for resident TX allocation origins.
The keepalive allocation path is handled separately by its observed source. -/
namespace Leanux.Proofs.WG.TransmitSecurity.PacketOrigins.NativeFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity
set_option maxHeartbeats 600000

theorem cookie_frame {action : WG.M α} (same : SameCookie action) : Preserves (Inv h) action := by
  apply frame
  apply snapshot_wire
  exact same.of_factor (fun s : WGOwnedView => txCryptWire {dev:=s.dev}) txCryptWire
    (fun w => by simp [txCryptWire,TxRing.nativeCell,TxDisposition.txPackets,cookieView,
      cookieDevice,wgOwnedView,wgStoreView,Option.map_map,Option.bind_map,Function.comp_def])

theorem cookie_reply (msg : List UInt8) (src : SkbSource) : Preserves (Inv h) (sendHandshakeCookie msg src) := by
  apply frame
  apply snapshot_wire
  exact (Cookies.sendHandshakeCookie_frame msg src).of_factor
    (fun s : Option Device × Nat × Nat => txCryptWire {dev:=s.1}) txCryptWire
    (fun w => by simp [txCryptWire,TxRing.nativeCell,TxDisposition.txPackets,
      Cookies.noiseView,Cookies.viewOfStore,Cookies.scrub,wgStoreView,Option.map_map,Option.bind_map,Function.comp_def])

macro "origin_handshake_frame" : tactic => `(tactic| first
  | (rx_retention_head beginSession; exact frame (snapshot_wire (OccurrenceKeys.session_wire _)))
  | (rx_retention_head createResponse; exact frame (snapshot_wire (OccurrenceKeys.create_response_wire _)))
  | (rx_retention_head addMacToPacket; exact frame (snapshot_wire (OccurrenceKeys.add_mac_wire _ _)))
  | (rx_retention_head sendBufferToPeer; exact frame (snapshot_wire (OccurrenceHandshake.buffer_wire _ _)))
  | (rx_retention_head timersSessionDerived; exact frame (snapshot_wire (OccurrenceHandshake.derived_wire _)))
  | (rx_retention_head timersTraversal; exact frame (snapshot_wire (timersTraversal_cryptWire _)))
  | (rx_retention_head timersAnyAuthenticatedPacketSent; exact frame (snapshot_wire (delTimer_cryptWire _ _)))
  | (rx_retention_head timersAnyAuthenticatedPacketReceived; exact frame (snapshot_wire (delTimer_cryptWire _ _)))
  | (rx_retention_head timersHandshakeComplete; exact frame (snapshot_wire (handshakeComplete_cryptWire _ _)))
  | (rx_retention_head sendHandshakeCookie; exact cookie_reply _ _)
  | (rx_retention_head consumeInitiation; exact frame (snapshot_wire (OccurrenceHandshake.consume_initiation_wire _)))
  | (rx_retention_head consumeResponse; exact frame (snapshot_wire (OccurrenceHandshake.consume_response_wire _)))
  | (rx_retention_head cookieMessageConsume; exact frame (snapshot_wire (OccurrenceHandshake.cookie_consume_wire _)))
  | (rx_retention_head setPeerEndpointFromSkb; exact frame (snapshot_wire (OccurrenceHandshake.endpoint_wire _ _)))
  | (rx_retention_head Cookies.loadPhase; exact store Cookies.loadPhase_sameStore)
  | (rx_retention_head cookieValidatePacket; exact cookie_frame (cookieValidatePacket_sameCookie _ _ _))
  | (rx_retention_head WG.orM; unfold WG.orM WG.andM; simp only [branch])
  | (rx_retention_head WG.andM; unfold WG.andM; simp only [branch])
  | (rx_retention_head branch; exact hoare_liftAmbient (AmbientM.branch _ _) _)
  | (rx_retention_head hiddenClock64; exact hoare_liftAmbient (AmbientM.hiddenClock64 _) _)
  | (rx_retention_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
  | origin_staging_frame)

end Leanux.Proofs.WG.TransmitSecurity.PacketOrigins.NativeFrames
