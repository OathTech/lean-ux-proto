import Leanux.Proofs.WG.HandshakeSecurity.H1Contracts

/-! Exact additional H1 projections for native exchange creation. These are
visible source dependencies, not an assumption that the security result holds. -/
namespace Leanux.Proofs.WG.HandshakeSecurity
open Leanux Leanux.WG

/-- Projection of H1 `Noise.createInitiation_tagMap_projected`: native
creation updates only this peer on success; normal refusal preserves all tags. -/
def H1CreateInitiationEdges : Prop :=
  ∀ (pid : PeerId) (w v : WGWorld) (a b : Ambient) (result : Option (List UInt8)),
    ((createInitiation pid).run w).run a = .ok ((result,v),b) →
    ∀ target, handshakeTagAt v target =
      if result.isSome ∧ target = pid then some HANDSHAKE_CREATED_INITIATION else handshakeTagAt w target

/-- Projection of H1 `Noise.consumeInitiation_tagMap_projected`: normal
successful initiation consumption restarts the returned peer's exchange. -/
def H1ConsumeInitiationEdges : Prop :=
  ∀ (msg : List UInt8) (w v : WGWorld) (a b : Ambient) (result : Option PeerId),
    ((consumeInitiation msg).run w).run a = .ok ((result,v),b) →
    ∀ target, handshakeTagAt v target =
      if result = some target then some HANDSHAKE_CONSUMED_INITIATION else handshakeTagAt w target

/-- Projection of H1 `Noise.createResponse_tagMap_projected`: creating a
response consumes a previously consumed initiation, preserving all other tags. -/
def H1CreateResponseEdges : Prop :=
  ∀ (pid : PeerId) (w v : WGWorld) (a b : Ambient) (result : Option (List UInt8)),
    ((createResponse pid).run w).run a = .ok ((result,v),b) →
    (result.isSome → handshakeTagAt w pid = some HANDSHAKE_CONSUMED_INITIATION) ∧
    (∀ target, handshakeTagAt v target =
      if result.isSome ∧ target = pid then some HANDSHAKE_CREATED_RESPONSE else handshakeTagAt w target)

structure H1ExchangeEdges : Prop where
  createInitiation : H1CreateInitiationEdges
  consumeInitiation : H1ConsumeInitiationEdges
  createResponse : H1CreateResponseEdges
  consumeResponse : H1ResponseEdges
  session : H1SessionEffects

end Leanux.Proofs.WG.HandshakeSecurity
