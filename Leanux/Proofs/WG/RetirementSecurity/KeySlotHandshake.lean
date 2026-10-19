import Leanux.Proofs.WG.RetirementSecurity.KeySlotConfiguration
import Leanux.Proofs.WG.RetirementSecurity.HolderReceiveFrames

/-! Complete original handshake receive transport includes authenticated
session creation, cookie replies, native keepalive staging and actual payment.
This liveness carrier does not treat handshake parsing as authentication. -/
namespace Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem derived (pid : PeerId) : Preserves (InvExcept pending) (timersSessionDerived pid) :=
  combined_frame (ConfiguredReceiveLeaves.timersSessionDerived_view pid) (HolderHandshake.derived_points pid)

theorem traversal (pid : PeerId) : Preserves (InvExcept pending) (timersTraversal pid) :=
  combined_frame (ConfiguredIdentity.timersTraversal_view pid) (timersTraversal_ownership pid)

theorem complete (pid : PeerId) (site : HiddenSite) :
    Preserves (InvExcept pending) (timersHandshakeComplete pid site) :=
  combined_frame (ConfiguredReceiveLeaves.timersHandshakeComplete_view pid site) (handshakeComplete_ownership pid site)

theorem received_timer (pid : PeerId) : Preserves (InvExcept pending) (timersDataReceived pid) := by
  unfold timersDataReceived
  simp (config := {zeta:=false}) only [branch,Functor.discard,map_const,
    Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (rx_retention_head modPeerTimer; exact mod_timer _ _ _ _)
    | key_slot_tx_step

theorem endpoint_source (pid : PeerId) (src : SkbSource) :
    Preserves (InvExcept pending) (setPeerEndpointFromSkb pid src) :=
  combined_frame (ConfiguredReceiveLeaves.setPeerEndpointFromSkb_view pid src) (HolderReceive.endpoint_points pid src)

theorem response (pid : PeerId) : Preserves (InvExcept pending) (sendHandshakeResponse pid) := by
  unfold sendHandshakeResponse
  simp (config := {zeta:=false}) only [branch,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head createResponse; exact create_response _)
    | (rx_retention_head addMacToPacket; exact add_mac _ _)
    | (rx_retention_head beginSession; exact session _)
    | (rx_retention_head timersSessionDerived; exact derived _)
    | (rx_retention_head timersTraversal; exact traversal _)
    | (rx_retention_head timersAnyAuthenticatedPacketSent; exact del_timer _ _)
    | (rx_retention_head sendBufferToPeer; exact buffer _ _)
    | key_slot_tx_step

theorem cookie_frame {action : WG.M α} (same : SameCookie action) : Preserves (InvExcept pending) action := by
  apply frame
  apply same.of_factor (fun s : WGOwnedView=>view {dev:=s.dev}) view
  intro w
  funext pid
  simp [view,peerAt,cookieView,cookieDevice,wgOwnedView,wgStoreView,Option.bind_map,Function.comp_def]

theorem cookie_reply (msg : List UInt8) (src : SkbSource) :
    Preserves (InvExcept pending) (sendHandshakeCookie msg src) := by
  apply frame
  apply (Cookies.sendHandshakeCookie_frame msg src).of_factor
    (fun s : Option Device × Nat × Nat=>view {dev:=s.1}) view
  intro w
  funext pid
  simp [view,peerAt,Cookies.noiseView,Cookies.viewOfStore,Cookies.scrub,wgStoreView,
    Option.bind_map,Function.comp_def]

theorem after_mac (msg : List UInt8) (src : SkbSource) (loaded : Bool) (state : MacState) :
    Preserves (InvExcept pending) (Cookies.afterMac msg src loaded state) := by
  unfold Cookies.afterMac
  simp (config := {zeta:=false}) only [branch,invariant,WG.andM,WG.orM]
  repeat' first
    | (rx_retention_head consumeInitiation; exact consume_initiation _)
    | (rx_retention_head consumeResponse; exact consume_response _)
    | (rx_retention_head sendHandshakeResponse; exact response _)
    | (rx_retention_head beginSession; exact session _)
    | (rx_retention_head sendHandshakeCookie; exact cookie_reply _ _)
    | (rx_retention_head setPeerEndpointFromSkb; exact endpoint_source _ _)
    | (rx_retention_head timersSessionDerived; exact derived _)
    | (rx_retention_head timersHandshakeComplete; exact complete _ _)
    | (rx_retention_head timersAnyAuthenticatedPacketReceived; exact del_timer _ _)
    | (rx_retention_head timersTraversal; exact traversal _)
    | (rx_retention_head sendKeepalive; exact keepalive _)
    | key_slot_tx_step

theorem receive_handshake (msg : List UInt8) (src : SkbSource) :
    Preserves (InvExcept pending) (receiveHandshakePacket msg src) := by
  rw [Cookies.receive_factor]
  simp (config := {zeta:=false}) only [branch]
  repeat' first
    | (rx_retention_head cookieMessageConsume; exact consume_cookie _)
    | (rx_retention_head Cookies.loadPhase; exact store Cookies.loadPhase_sameStore)
    | (rx_retention_head cookieValidatePacket; exact cookie_frame (cookieValidatePacket_sameCookie _ _ _))
    | (rx_retention_head Cookies.afterMac; exact after_mac _ _ _ _)
    | key_slot_tx_step

theorem receive_step : Preserves (InvExcept pending) WG.receiveStep := by
  unfold WG.receiveStep
  simp (config := {zeta:=false}) only [branch]
  repeat' first
    | (rx_retention_head receiveHandshakePacket; exact receive_handshake _ _)
    | key_slot_tx_step

end Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
