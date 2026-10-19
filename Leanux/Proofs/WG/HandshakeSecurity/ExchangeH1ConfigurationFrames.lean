import Leanux.Proofs.WG.HandshakeSecurity.ExchangeH1ControlFrames

/-! Configuration projections from C2 H1 at `5177bd9c`. Allocation may replace
a numeric peer location but initializes its handshake to zero; these native
facts assume neither initialized reachability nor a prior exchange history. -/
namespace Leanux.Proofs.WG.HandshakeSecurity
open Leanux Leanux.WG

structure H1ConfigurationTagFrames : Prop where
  /-- C2 `Noise.DriverTags.setAllowedip_frame`, pin `5177bd9c`. -/
  allowed : ∀ pid ip, H1TagSame (setAllowedip pid ip)
  /-- C2 `Noise.DriverTags.removeByPeer_frame`, pin `5177bd9c`. -/
  removeIps : ∀ pid, H1TagSame (removeByPeer pid)
  /-- C2 `Noise.DriverTags.setPeerEndpoint_frame`, pin `5177bd9c`. -/
  endpoint : ∀ pid endpoint, H1TagSame (setPeerEndpoint pid endpoint)
  /-- C2 `Noise.DriverTags.peerGet_frame`, pin `5177bd9c`. -/
  peerGet : ∀ pid, H1TagSame (WG.peerGet pid)
  /-- C2 `Noise.peerCreate_tag_map`, pin `5177bd9c`, projected to surviving
  nonzero tags. The returned location is zero even on cursor overwrite. -/
  create : ∀ key psk, H1TagRetains (peerCreate key psk)
  /-- C2 `Noise.DriverTags.precomputeStaticStatic_frame`, pin `5177bd9c`. -/
  precompute : ∀ pid, H1TagSame (precomputeStaticStatic pid)
  /-- C2 `Noise.expireCurrentPeerKeypairs_tagMap_projected`, pin `5177bd9c`,
  projected to surviving nonzero tags. -/
  expire : ∀ pid, H1TagRetains (expireCurrentPeerKeypairs pid)
  /-- C2 `Noise.DriverTags.clearPeerEndpointSrc_frame`, pin `5177bd9c`. -/
  clearEndpoint : ∀ pid, H1TagSame (clearPeerEndpointSrc pid)
  /-- C2 `Noise.DriverTags.setPort_frame`, pin `5177bd9c`. -/
  port : ∀ port, H1TagSame (setPort port)

end Leanux.Proofs.WG.HandshakeSecurity
