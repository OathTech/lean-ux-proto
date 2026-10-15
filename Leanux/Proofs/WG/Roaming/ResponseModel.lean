import Leanux.Proofs.WG.Campaign2.View
import Leanux.WG.Receive

namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG

def responseFirst (ck input : List UInt8) : List UInt8 :=
  hmacBlake2s (hmacBlake2s ck input) [1]
def responseSecond (ck input : List UInt8) : List UInt8 :=
  hmacBlake2s (hmacBlake2s ck input) (responseFirst ck input ++ [2])
def responseThird (ck input : List UInt8) : List UInt8 :=
  hmacBlake2s (hmacBlake2s ck input) (responseSecond ck input ++ [3])
def responseEphemeral (msg : List UInt8) := (msg.drop 12).take 32
def responseEeChain (msg : List UInt8) (p : Peer) :=
  responseFirst (responseFirst p.chainingKey (responseEphemeral msg))
    (curve25519 p.ephemeralPrivate (responseEphemeral msg)).1
def responseSeChain (msg : List UInt8) (identity : StaticIdentity) (p : Peer) :=
  responseFirst (responseEeChain msg p)
    (curve25519 identity.staticPrivate (responseEphemeral msg)).1
def responseAad (msg : List UInt8) (identity : StaticIdentity) (p : Peer) :=
  noiseHash (noiseHash (p.hash ++ responseEphemeral msg) ++
    responseSecond (responseSeChain msg identity p) p.presharedKey)
def responseKey (msg : List UInt8) (identity : StaticIdentity) (p : Peer) :=
  responseThird (responseSeChain msg identity p) p.presharedKey

/-- The lookup owner and the referenced peer are kept separate; no equality or inequality is assumed. -/
structure ResponseInput where
  identity : StaticIdentity
  owner : PeerId
  pid : PeerId
  peer : Peer

/-- Exact crypto input equations for the successful response path. No outer
source address is an AEAD input. The state recheck and commit are stated separately. -/
def ResponseCrypto (msg : List UInt8) (input : ResponseInput) : Prop :=
  input.identity.hasIdentity = true ∧
  input.peer.handshakeState = HANDSHAKE_CREATED_INITIATION ∧
  (curve25519 input.peer.ephemeralPrivate (responseEphemeral msg)).2 = true ∧
  (curve25519 input.identity.staticPrivate (responseEphemeral msg)).2 = true ∧
  aeadDecrypt (responseKey msg input.identity input.peer) noiseNonce
    ((msg.drop 44).take 16) (responseAad msg input.identity input.peer) = some []

structure ResponseConsumed where
  input : ResponseInput
  rechecked : Peer
  committed : Campaign2.Snapshot

def ResponseConsumedFacts (msg : List UInt8) (out : ResponseConsumed) : Prop :=
  ResponseCrypto msg out.input ∧
  out.rechecked.handshakeState = out.input.peer.handshakeState ∧
  ∃ p, (out.committed.wg.device.bind fun d => d.peers[out.input.pid]?) = some p ∧
    p.handshakeState = HANDSHAKE_CONSUMED_RESPONSE ∧
    p.remoteEphemeral = responseEphemeral msg ∧ p.remoteIndex = u32le msg 4 ∧
    p.chainingKey = responseFirst (responseSeChain msg out.input.identity out.input.peer)
      out.input.peer.presharedKey ∧
    p.hash = noiseHash (responseAad msg out.input.identity out.input.peer ++ ((msg.drop 44).take 16))

structure ResponseLookupRead where
  before : Campaign2.Snapshot
  observed : Campaign2.Outcome (Option (IndexOwner × PeerId))
  entry : Option (IndexOwner × PeerId)
  after : Campaign2.Snapshot

structure ResponseLookupCut where
  input : ResponseInput
  lookup : ResponseLookupRead

def ResponseLookupFacts (cut : ResponseLookupCut) : Prop :=
  cut.lookup.entry = some (.handshake cut.input.owner, cut.input.pid) ∧
  cut.lookup.observed = .ok (cut.lookup.entry, cut.lookup.after) ∧
  (cut.lookup.before.wg.device.map Device.staticIdentity) = some cut.input.identity ∧
  (cut.lookup.after.wg.device.bind fun d => d.peers[cut.input.pid]?) = some cut.input.peer ∧
  cut.input.identity.hasIdentity = true ∧
  cut.input.peer.handshakeState = HANDSHAKE_CREATED_INITIATION

structure ResponseCallCut where
  underLoad : Bool
  mac : MacState
  lookup : ResponseLookupCut
  consumed : ResponseConsumed
  beforeSetter : Campaign2.Snapshot

def ResponseCallFacts (msg : List UInt8) (cut : ResponseCallCut) : Prop :=
  ((cut.underLoad = true ∧ cut.mac = .withCookie) ∨
    (cut.underLoad = false ∧ cut.mac = .noCookie)) ∧
  ResponseLookupFacts cut.lookup ∧ cut.consumed.input = cut.lookup.input ∧
  ResponseConsumedFacts msg cut.consumed ∧
  cut.beforeSetter.wg.device = cut.consumed.committed.wg.device

/-- Normal full-caller completion has a successful prefix observation. A
present cut is the actual setter boundary; a missing cut takes the pure suffix. -/
def ResponseCallObservation (msg : List UInt8)
    (observed : Campaign2.Outcome (Option ResponseCallCut)) : Prop :=
  ∃ candidate atCut, observed = .ok (candidate, atCut) ∧
    ∀ cut, candidate = some cut → cut.beforeSetter = atCut ∧ ResponseCallFacts msg cut

end Leanux.Proofs.WG.Roaming
