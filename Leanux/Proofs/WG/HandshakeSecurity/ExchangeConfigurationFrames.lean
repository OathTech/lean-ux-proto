import Leanux.Proofs.WG.HandshakeSecurity.ExchangeH1ConfigurationFrames

/-! Canonical configuration and native Boolean guard frames for the exchange
projection. Peer update callbacks use the actual saved peer read separately. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Exchange
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem configuration_frame (h : List Event) (action : WG.M α) (same : SameConfiguration action) :
    Framing.Preserves (StateInv h) action := by
  apply frame_tag h action
  apply same.of_factor
    (fun s : WGOwnedView => fun pid => (s.dev.bind fun d => d.peers[pid]?).map Peer.handshakeState)
    handshakeTagAt
  intro w
  simp only [configurationView,configurationDevice,wgOwnedView,wgStoreView,
    Option.bind_map,Function.comp_def]
  rfl

end Leanux.Proofs.WG.HandshakeSecurity.Exchange
