import Leanux.Proofs.WG.Roaming.PollEndpointModel

namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Campaign2

/-- Admission reads immediately before this iteration's designated setter. -/
structure PollAttemptCut where
  id : SkbId
  packet : RxPacket
  endpoint : Endpoint
  beforeRead : Snapshot
  beforeCounter : Snapshot
  afterCounter : Snapshot
  counter : Outcome Bool
  beforeSetter : Snapshot

inductive PollAttemptPrepared where
  | drained
  | rejected (id : SkbId) (packet : RxPacket)
  | endpoint (cut : PollAttemptCut)

/-- Every attempted iteration is recorded, including a failing prefix.
A successful prefix records its actual suffix outcome, even when that fails. -/
structure PollAttemptIteration where
  entry : Snapshot
  admission : Outcome PollAttemptPrepared
  continuation : Option (Outcome (ForInStep PollState))

def PollAttemptFacts (pid : PeerId) (entry : Snapshot) (cut : PollAttemptCut) : Prop :=
  packetAt entry cut.id = some cut.packet ∧
  packetAt cut.beforeRead cut.id = some cut.packet ∧
  cut.packet.peer = pid ∧ cut.packet.state = .crypted ∧
  cut.counter = .ok (true, cut.afterCounter) ∧
  cut.endpoint = sourceEndpoint cut.packet.source ∧
  (cut.packet.source.family = 4 ∨ cut.packet.source.family = 6)

def PollAttemptIterationFacts (pid : PeerId) (iteration : PollAttemptIteration) : Prop :=
  (∀ error, iteration.admission = .error error → iteration.continuation = none) ∧
  (∀ prepared atCut, iteration.admission = .ok (prepared, atCut) → iteration.continuation.isSome) ∧
  ∀ cut atCut, iteration.admission = .ok (.endpoint cut, atCut) →
    cut.beforeSetter = atCut ∧ PollAttemptFacts pid iteration.entry cut

structure PollAttemptAudit where
  iterations : List PollAttemptIteration
  outcome : Outcome Nat

end Leanux.Proofs.WG.Roaming
