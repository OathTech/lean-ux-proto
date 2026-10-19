import Leanux.Proofs.WG.HandshakeSecurity.ExchangeH1Frames

/-! Native data-path projections of campaign 2 H1 dependencies at `5177bd9c`.
Deletion or zeroing is permitted; a surviving nonzero handshake tag cannot be
restored to an older exchange by these native actions. -/
namespace Leanux.Proofs.WG.HandshakeSecurity
open Leanux Leanux.WG

abbrev H1TagRetains (action : WG.M α) : Prop :=
  ∀ w v a b result, (action.run w).run a = .ok ((result,v),b) → Exchange.Retains w v

structure H1DataTagFrames : Prop where
  /-- C2 `Index.sendStagedPackets_tags_retained`, pin `5177bd9c`. -/
  staging : ∀ pid, H1TagRetains (sendStagedPackets pid)
  /-- C2 `Index.sendKeepalive_tags_retained`, pin `5177bd9c`. -/
  keepalive : ∀ pid, H1TagRetains (sendKeepalive pid)
  /-- C2 `Noise.DriverTags.Silent.consumeDataDone_retained`, pin `5177bd9c`,
  instantiated with the actual entry tag map and its reflexive retention. -/
  consume : ∀ pid pkt ep, H1TagRetains (consumeDataDone pid pkt ep)

end Leanux.Proofs.WG.HandshakeSecurity
