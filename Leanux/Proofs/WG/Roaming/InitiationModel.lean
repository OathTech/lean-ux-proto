import Leanux.Proofs.WG.Roaming.ResponseModel

namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Campaign2

def initiationEphemeral (msg : List UInt8) := (msg.drop 8).take 32
def initiationEsInput (msg : List UInt8) := responseFirst handshakeInitChainingKey (initiationEphemeral msg)
def initiationDh (msg : List UInt8) (identity : StaticIdentity) :=
  curve25519 identity.staticPrivate (initiationEphemeral msg)
def initiationEsChain (msg : List UInt8) (identity : StaticIdentity) :=
  responseFirst (initiationEsInput msg) (initiationDh msg identity).1
def initiationStaticKey (msg : List UInt8) (identity : StaticIdentity) :=
  responseSecond (initiationEsInput msg) (initiationDh msg identity).1
def initiationStaticAad (msg : List UInt8) (identity : StaticIdentity) :=
  noiseHash (noiseHash (handshakeInitHash ++ identity.staticPublic) ++ initiationEphemeral msg)
def initiationTimestampAad (msg : List UInt8) (identity : StaticIdentity) :=
  noiseHash (initiationStaticAad msg identity ++ ((msg.drop 40).take 48))

structure InitiationLookup where
  before : Snapshot
  observed : Outcome (Option PeerId)
  result : Option PeerId
  after : Snapshot

def InitiationLookupFacts (key : Key) (pid : PeerId) (out : InitiationLookup) : Prop :=
  out.result = some pid ∧ out.observed = .ok (some pid, out.after) ∧
  ∃ d p, out.before.wg.device = some d ∧
    d.peerHashtable.find? (·.1 == key) = some (key, pid) ∧
    d.peers[pid]? = some p ∧ 0 < p.refcount ∧ p.refcount + 1 < 2^31 ∧
    out.after.wg.device = some { d with peers := d.peers.insert pid { p with refcount := p.refcount + 1 } }

structure InitiationConsumed where
  identity : StaticIdentity
  staticPlain : Key
  timestamp : List UInt8
  pid : PeerId
  lookup : InitiationLookup
  dhPeer : Peer
  beforeDh : Snapshot
  checked : Peer
  beforeChecks : Snapshot
  floodNow : Int64
  consumption : Int64
  committed : Snapshot

def InitiationCommitFacts (msg ck hash : List UInt8) (out : InitiationConsumed) : Prop :=
  out.beforeChecks.peerAt out.pid = some out.checked ∧
  memcmp out.timestamp out.checked.latestTimestamp = .gt ∧
  out.checked.lastInitiationConsumption + NSEC_PER_SEC64 / INITIATIONS_PER_SECOND.toInt64 ≤ out.floodNow ∧
  ∃ p, out.committed.peerAt out.pid = some p ∧
    p.handshakeState = HANDSHAKE_CONSUMED_INITIATION ∧
    p.remoteEphemeral = initiationEphemeral msg ∧ p.remoteIndex = u32le msg 4 ∧
    p.latestTimestamp = out.timestamp ∧
    p.chainingKey = ck ∧
    p.hash = hash ∧
    p.lastInitiationConsumption =
      (if out.checked.lastInitiationConsumption - out.consumption < 0 then out.consumption
       else out.checked.lastInitiationConsumption)


/-- Actual decrypt and gate values, with no fixed-length or table/store
coherence assumption. Clock comparisons retain signed wrapping arithmetic. -/
def InitiationConsumedFacts (msg : List UInt8) (out : InitiationConsumed) : Prop :=
  out.identity.hasIdentity = true ∧
  (initiationDh msg out.identity).2 = true ∧
  aeadDecrypt (initiationStaticKey msg out.identity) noiseNonce
    ((msg.drop 40).take 48) (initiationStaticAad msg out.identity) = some out.staticPlain ∧
  InitiationLookupFacts out.staticPlain out.pid out.lookup ∧
  out.beforeDh.peerAt out.pid = some out.dhPeer ∧
  out.dhPeer.precomputedStaticStatic ≠ List.replicate 32 0 ∧
  aeadDecrypt (responseSecond (initiationEsChain msg out.identity) out.dhPeer.precomputedStaticStatic)
    noiseNonce ((msg.drop 88).take 28) (initiationTimestampAad msg out.identity) = some out.timestamp ∧
  InitiationCommitFacts msg
    (responseFirst (initiationEsChain msg out.identity) out.dhPeer.precomputedStaticStatic)
    (noiseHash (initiationTimestampAad msg out.identity ++ ((msg.drop 88).take 28))) out

structure InitiationCallCut where
  underLoad : Bool
  mac : MacState
  consumed : InitiationConsumed
  beforeSetter : Snapshot

def InitiationCallFacts (msg : List UInt8) (cut : InitiationCallCut) : Prop :=
  ((cut.underLoad = true ∧ cut.mac = .withCookie) ∨
    (cut.underLoad = false ∧ cut.mac = .noCookie)) ∧
  InitiationConsumedFacts msg cut.consumed ∧
  cut.beforeSetter.wg.device = cut.consumed.committed.wg.device

def InitiationCallObservation (msg : List UInt8)
    (observed : Outcome (Option InitiationCallCut)) : Prop :=
  ∃ candidate atCut, observed = .ok (candidate, atCut) ∧
    ∀ cut, candidate = some cut → cut.beforeSetter = atCut ∧ InitiationCallFacts msg cut

end Leanux.Proofs.WG.Roaming
