import Leanux.Proofs.WG.HandshakeSecurity.ResponderHandshakeSend

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.HandshakeControl
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Queues.RxCredits

macro "responder_control_step" : tactic => `(tactic| first
  | (receive_update_head setPeer
     apply modifyPeer
     all_goals intro p; rfl)
  | (receive_update_head Bind.bind
     apply modifyPeer_bind
     · intro p; rfl
     · intro p; rfl
     · intro p; rfl
     intro x)
  | (rx_retention_head getDev; exact store getDev_sameWGStore)
  | (rx_retention_head getPeer
     exact (pinned_const _private.Leanux.Proofs.WG.Origins.ConfiguredReceive.«0».Leanux.Proofs.WG.ConfiguredReceive.getPeer_preserves) _ _)
  | (rx_retention_head modifyDev
     apply modifyDevice
     all_goals intro d; rfl)
  | (rx_retention_head peerPut; exact pay _)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | routing_tx_step)

theorem sendResponse (H1 : H1ResponderCurrentEdges) (pid : PeerId) :
    Preserves (Inv confirmed) (sendHandshakeResponse pid) := by
  unfold sendHandshakeResponse
  simp (config := {zeta := false}) only [hiddenClock64, branch, invariant]
  repeat' first
    | (rx_retention_head createResponse; exact create _)
    | (rx_retention_head addMacToPacket; exact mac _ _)
    | (rx_retention_head beginSession; exact session H1 _)
    | (rx_retention_head timersSessionDerived; exact derived _)
    | (rx_retention_head timersTraversal; exact traversal _)
    | (rx_retention_head timersAnyAuthenticatedPacketSent; exact sent _)
    | (rx_retention_head sendBufferToPeer; exact sendBuffer _ _)
    | responder_control_step

theorem afterMac (H1 : H1ResponderCurrentEdges) (msg : List UInt8)
    (src : SkbSource) (loaded : Bool) (state : MacState) :
    Preserves (Inv confirmed) (Cookies.afterMac msg src loaded state) := by
  unfold Cookies.afterMac
  simp (config := {zeta := false}) only [branch, invariant, WG.andM, WG.orM]
  repeat' first
    | (rx_retention_head consumeInitiation; exact initiation _)
    | (rx_retention_head consumeResponse; exact response _)
    | (rx_retention_head sendHandshakeResponse; exact sendResponse H1 _)
    | (rx_retention_head beginSession; exact session H1 _)
    | (rx_retention_head sendHandshakeCookie; exact sendCookie _ _)
    | (rx_retention_head setPeerEndpointFromSkb; exact endpoint _ _)
    | (rx_retention_head timersSessionDerived; exact derived _)
    | (rx_retention_head timersHandshakeComplete; exact complete _ _)
    | (rx_retention_head sendKeepalive; exact keepalive _)
    | (rx_retention_head timersAnyAuthenticatedPacketReceived; exact received _)
    | (rx_retention_head timersTraversal; exact traversal _)
    | responder_control_step

theorem receive (H1 : H1ResponderCurrentEdges) (msg : List UInt8) (src : SkbSource) :
    Preserves (Inv confirmed) (receiveHandshakePacket msg src) := by
  rw [Cookies.receive_factor]
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head cookieMessageConsume; exact consumeCookie _)
    | (rx_retention_head Cookies.loadPhase; exact store Cookies.loadPhase_sameStore)
    | (rx_retention_head cookieValidatePacket; exact cookie (cookieValidatePacket_sameCookie _ _ _))
    | (rx_retention_head Cookies.afterMac; exact afterMac H1 _ _ _ _)
    | responder_control_step

/-- This is the real native handshake actor. Its C1 entry carrier supplies
configured identity and slot bounds at every actual session callback. -/
theorem step (H1 : H1ResponderCurrentEdges) : Preserves (Inv confirmed) WG.receiveStep := by
  unfold WG.receiveStep
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head receiveHandshakePacket; exact receive H1 _ _)
    | responder_control_step

end Leanux.Proofs.WG.HandshakeSecurity.Responder.HandshakeControl
