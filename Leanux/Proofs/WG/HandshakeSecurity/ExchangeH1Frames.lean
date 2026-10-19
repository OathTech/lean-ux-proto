import Leanux.Proofs.WG.HandshakeSecurity.ExchangeNativeFrames

/-! Named projections of campaign 2 H1 at `5177bd9cbcaffb16dcf8290d88c0e5e0544a0939`.
Only native operational tag frames occur in this package. No initialized ledger,
reachability, authentication or replay-security conclusion is assumed. -/
namespace Leanux.Proofs.WG.HandshakeSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing

abbrev H1TagSame (action : WG.M α) : Prop := SameView handshakeTagAt action

structure H1HandshakeTagFrames : Prop where
  /-- C2 `Noise.addMacToPacket_spec_tagMap_variant`, pin `5177bd9c`. -/
  mac : ∀ pid msg, H1TagSame (addMacToPacket pid msg)
  /-- C2 `Noise.sendBufferToPeer_spec_tagMap_variant`, pin `5177bd9c`. -/
  send : ∀ pid msg, H1TagSame (sendBufferToPeer pid msg)
  /-- C2 `Noise.ResponseSuffix.traversal_tag_frame`, pin `5177bd9c`. -/
  traversal : ∀ pid, H1TagSame (timersTraversal pid)
  /-- C2 `Noise.InitiationCaller.timersHandshakeInitiated_spec_tagMap_variant`, pin `5177bd9c`. -/
  initiated : ∀ pid, H1TagSame (timersHandshakeInitiated pid)
  /-- C2 `Noise.ResponseSuffix.derived_tag_frame`, pin `5177bd9c`. -/
  derived : ∀ pid, H1TagSame (timersSessionDerived pid)
  /-- C2 `Noise.ResponseSuffix.delTimer_tag_frame`, pin `5177bd9c`. -/
  deleteTimer : ∀ pid timer, H1TagSame (delTimer pid timer)
  /-- C2 `Noise.ReceptionTagSupport.setPeerEndpointFromSkb_tag_frame`, pin `5177bd9c`. -/
  endpoint : ∀ pid src, H1TagSame (setPeerEndpointFromSkb pid src)
  /-- C2 `Noise.ReceptionTagSupport.handshakeComplete_tag_frame`, pin `5177bd9c`. -/
  complete : ∀ pid site, H1TagSame (timersHandshakeComplete pid site)
  /-- C2 `Noise.ReceptionTagSupport.cookieMessageConsume_tag_frame`, pin `5177bd9c`. -/
  cookieConsume : ∀ msg, H1TagSame (cookieMessageConsume msg)
  /-- C2 `Noise.sendHandshakeCookie_spec_tagMap_variant`, pin `5177bd9c`. -/
  cookie : ∀ msg src, H1TagSame (sendHandshakeCookie msg src)
  /-- C2 `Noise.cookieValidatePacket_spec_tagMap_variant`, pin `5177bd9c`. -/
  validate : ∀ msg src loaded, H1TagSame (cookieValidatePacket msg src loaded)

end Leanux.Proofs.WG.HandshakeSecurity
