import Leanux.Proofs.WG.HandshakeSecurity.ExchangeH1ControlFrames

/-! Collection of the named C2 H1 source projections used by the shared-driver
composition. Every component is a native per-call edge or tag frame; the C3
exchange history and initialized reachability are never assumptions here. -/
namespace Leanux.Proofs.WG.HandshakeSecurity

structure H1DriverSourceFacts : Prop where
  /-- Native create/consume/install edges, with exact C2 declarations named in `H1ExchangeEdges`. -/
  edges : H1ExchangeEdges
  /-- Native handshake suffix frames pinned in `H1HandshakeTagFrames`. -/
  handshake : H1HandshakeTagFrames
  /-- Native staging/keepalive/data receive frames pinned in `H1DataTagFrames`. -/
  data : H1DataTagFrames
  /-- Native data-worker and NAPI frames pinned in `H1WorkerTagFrames`. -/
  workers : H1WorkerTagFrames
  /-- Native timer and clearing frames pinned in `H1ControlTagFrames`. -/
  control : H1ControlTagFrames

end Leanux.Proofs.WG.HandshakeSecurity
