import Leanux.Proofs.WG.HandshakeSecurity.Observation

/-! The retained-peer security view excludes accounting and borrowed references. -/
namespace Leanux.Proofs.WG.HandshakeSecurity
open Leanux Leanux.WG

structure HandshakeView where
  identity : Nat
  timestamp : List UInt8
  lastConsumption : Int64
  state : Nat
  ephemeral : List UInt8
  remoteEphemeral : List UInt8
  hash : List UInt8
  chainingKey : List UInt8
  remoteIndex : Nat
  current : Option KeypairId
  previous : Option KeypairId
  next : Option KeypairId
  deriving DecidableEq

def handshakeView (p : Peer) : HandshakeView :=
  ⟨p.internalId, p.latestTimestamp, p.lastInitiationConsumption,
    p.handshakeState, p.ephemeralPrivate, p.remoteEphemeral, p.hash,
    p.chainingKey, p.remoteIndex, p.keypairCurrent, p.keypairPrevious, p.keypairNext⟩

def peerView (w : WGWorld) (pid : PeerId) : Option HandshakeView :=
  (w.dev.bind fun d => d.peers[pid]?).map handshakeView

end Leanux.Proofs.WG.HandshakeSecurity
