import Leanux.Proofs.WG.Roaming.InitiationLookupProductModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.Product
open Leanux Leanux.WG

structure InitiationConsumed where
  identity : StaticIdentity
  staticPlain : Key
  timestamp : List UInt8
  pid : PeerId
  lookup : InitiationLookup
  dhPeer : Peer
  beforeDh : Campaign2.Product.Snapshot
  checked : Peer
  beforeChecks : Campaign2.Product.Snapshot
  floodNow : Int64
  consumption : Int64
  committed : Campaign2.Product.Snapshot

def nativeInitiationLookup (out : InitiationLookup) : Roaming.InitiationLookup where
  before := out.before.toSnapshot
  observed := out.observed.map fun (result, state) => (result, state.toSnapshot)
  result := out.result
  after := out.after.toSnapshot

def restoreInitiationLookup (fixture : Campaign2.Product.Fixture) (out : Roaming.InitiationLookup) :
    InitiationLookup where
  before := {toSnapshot := out.before, fixture}
  observed := out.observed.map fun (result, state) => (result, {toSnapshot := state, fixture})
  result := out.result
  after := {toSnapshot := out.after, fixture}

/-- Supplied observations remain independent of the actual entry fixture.
Only observations captured by the tail receive that fixture. -/
def restoreInitiationFinish (fixture : Campaign2.Product.Fixture) (lookup : InitiationLookup)
    (beforeDh : Campaign2.Product.Snapshot) (out : Roaming.InitiationConsumed) : InitiationConsumed where
  identity := out.identity
  staticPlain := out.staticPlain
  timestamp := out.timestamp
  pid := out.pid
  lookup := lookup
  dhPeer := out.dhPeer
  beforeDh := beforeDh
  checked := out.checked
  beforeChecks := {toSnapshot := out.beforeChecks, fixture}
  floodNow := out.floodNow
  consumption := out.consumption
  committed := {toSnapshot := out.committed, fixture}

def InitiationCommitFacts (msg ck hash : List UInt8) (out : InitiationConsumed) : Prop :=
  out.beforeChecks.toSnapshot.peerAt out.pid = some out.checked ∧
  memcmp out.timestamp out.checked.latestTimestamp = .gt ∧
  out.checked.lastInitiationConsumption + NSEC_PER_SEC64 / INITIATIONS_PER_SECOND.toInt64 ≤ out.floodNow ∧
  ∃ p, out.committed.toSnapshot.peerAt out.pid = some p ∧
    p.handshakeState = HANDSHAKE_CONSUMED_INITIATION ∧
    p.remoteEphemeral = initiationEphemeral msg ∧ p.remoteIndex = u32le msg 4 ∧
    p.latestTimestamp = out.timestamp ∧ p.chainingKey = ck ∧ p.hash = hash ∧
    p.lastInitiationConsumption =
      (if out.checked.lastInitiationConsumption - out.consumption < 0 then out.consumption
       else out.checked.lastInitiationConsumption)


def restoreInitiationConsume (fixture : Campaign2.Product.Fixture) (out : Roaming.InitiationConsumed) :
    InitiationConsumed :=
  restoreInitiationFinish fixture (restoreInitiationLookup fixture out.lookup)
    {toSnapshot := out.beforeDh, fixture} out

def InitiationConsumedFacts (msg : List UInt8) (out : InitiationConsumed) : Prop :=
  out.identity.hasIdentity = true ∧
  (initiationDh msg out.identity).2 = true ∧
  aeadDecrypt (initiationStaticKey msg out.identity) noiseNonce
    ((msg.drop 40).take 48) (initiationStaticAad msg out.identity) = some out.staticPlain ∧
  InitiationLookupFacts out.staticPlain out.pid out.lookup ∧
  out.beforeDh.toSnapshot.peerAt out.pid = some out.dhPeer ∧
  out.dhPeer.precomputedStaticStatic ≠ List.replicate 32 0 ∧
  aeadDecrypt (responseSecond (initiationEsChain msg out.identity) out.dhPeer.precomputedStaticStatic)
    noiseNonce ((msg.drop 88).take 28) (initiationTimestampAad msg out.identity) = some out.timestamp ∧
  InitiationCommitFacts msg
    (responseFirst (initiationEsChain msg out.identity) out.dhPeer.precomputedStaticStatic)
    (noiseHash (initiationTimestampAad msg out.identity ++ ((msg.drop 88).take 28))) out

end Leanux.Proofs.WG.Roaming.Product
