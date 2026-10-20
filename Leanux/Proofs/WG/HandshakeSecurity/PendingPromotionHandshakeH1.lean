import Leanux.Proofs.WG.HandshakeSecurity.PendingPromotionReceive

namespace Leanux.Proofs.WG.HandshakeSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

/-- Single-call pending-slot frames at C2 pin
`be8c209c`. Each citation is a native
projected-state fact. The initialized history and its distinctness are not
assumptions of this package. -/
structure H1PendingHandshakeFrames : Prop where
  /-- `Noise.PendingTickets.consumeInitiation_frame`. -/
  initiation : ∀ msg, SameView PendingPromotion.view (consumeInitiation msg)
  /-- `Noise.PendingTickets.consumeResponse_frame`. -/
  response : ∀ msg, SameView PendingPromotion.view (consumeResponse msg)
  /-- `Noise.PendingReception.cookieMessageConsume_pending`. -/
  cookie : ∀ msg, ProjectedAction PendingPromotion.view Retained (cookieMessageConsume msg)
  /-- `Noise.PendingTickets.createResponse_frame`. -/
  create : ∀ pid, SameView PendingPromotion.view (createResponse pid)
  /-- `Noise.PendingTickets.addMacToPacket_frame`. -/
  mac : ∀ pid msg, SameView PendingPromotion.view (addMacToPacket pid msg)
  /-- `Noise.PendingTickets.sendBufferToPeer_frame`. -/
  send : ∀ pid msg, SameView PendingPromotion.view (sendBufferToPeer pid msg)
  /-- `Noise.PendingTickets.timersSessionDerived_frame`. -/
  derived : ∀ pid, SameView PendingPromotion.view (timersSessionDerived pid)
  /-- `Noise.PendingTickets.timersTraversal_frame`. -/
  traversal : ∀ pid, SameView PendingPromotion.view (timersTraversal pid)
  /-- `Noise.PendingTickets.timersAnyAuthenticatedPacketSent_frame`. -/
  sent : ∀ pid, SameView PendingPromotion.view (timersAnyAuthenticatedPacketSent pid)
  /-- `Noise.PendingTickets.timersAnyAuthenticatedPacketReceived_frame`. -/
  received : ∀ pid, SameView PendingPromotion.view (timersAnyAuthenticatedPacketReceived pid)
  /-- `Noise.PendingTickets.timersHandshakeComplete_frame`. -/
  complete : ∀ pid site, SameView PendingPromotion.view (timersHandshakeComplete pid site)
  /-- `Noise.PendingTickets.setPeerEndpointFromSkb_frame`. -/
  endpoint : ∀ pid src, SameView PendingPromotion.view (setPeerEndpointFromSkb pid src)

end Leanux.Proofs.WG.HandshakeSecurity
