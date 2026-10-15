import Leanux.Proofs.WG.Roaming.PublicationModel
import Leanux.Proofs.WG.Roaming.View

namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Campaign2

abbrev PollState := Nat × GroState × Bool

/-- The actual first poll packet and the admission reads before its endpoint setter. -/
structure PollEndpointCut where
  id : SkbId
  packet : RxPacket
  endpoint : Endpoint
  beforeRead : Snapshot
  beforeCounter : Snapshot
  afterCounter : Snapshot
  counter : Outcome Bool
  atEndpoint : Snapshot

def PollEndpointFacts (pid : PeerId) (entry : Snapshot) (cut : PollEndpointCut) : Prop :=
  packetAt entry cut.id = some cut.packet ∧
  packetAt cut.beforeRead cut.id = some cut.packet ∧
  cut.packet.peer = pid ∧ cut.packet.state = .crypted ∧
  cut.counter = .ok (true, cut.afterCounter) ∧
  cut.endpoint = sourceEndpoint cut.packet.source ∧
  (cut.packet.source.family = 4 ∨ cut.packet.source.family = 6) ∧
  remoteAt cut.atEndpoint pid = some (destination cut.endpoint)

inductive PollPrepared where
  | drained
  | rejected (id : SkbId) (packet : RxPacket)
  | endpoint (cut : PollEndpointCut)

def PollPrepared.endpoint? : PollPrepared → Option PollEndpointCut
  | .endpoint cut => some cut
  | _ => none

/-- On normal full-poll return, its budget-guarded first prefix succeeded.
Endpoint facts refer to the immediate setter cut, not the final poll state. -/
def PollEndpointObservation (pid : PeerId) (budget : Nat) (entry : Snapshot)
    (result : Nat × Outcome (Option PollPrepared)) : Prop :=
  ∃ prepared atCut, result.2 = .ok (prepared, atCut) ∧
    ∀ cut, prepared = some (.endpoint cut) →
      budget ≠ 0 ∧ PollEndpointFacts pid entry cut

/-- Historical decryption-key provenance for the packet selected by this poll.
This does not identify the packet peer with the dereferenced publication owner. -/
def PollEndpointAuthentication (pub : PublicationCut) (cut : PollEndpointCut) : Prop :=
  ∃ key, keyAt pub.beforeDecrypt pub.input.keypair = some key ∧
    cut.packet.source = pub.input.source ∧
    cut.packet.peer = pub.input.peer ∧
    cut.packet.keypair = pub.input.keypair ∧
    cut.packet.nonce = u64le pub.input.bytes 8 ∧
    aeadDecrypt key.receiving.key (counterNonce (u64le pub.input.bytes 8))
      (pub.input.bytes.drop 16) [] = some cut.packet.bytes

abbrev PublicationPollResult :=
  Bool × Option (PublicationCut × (Nat × Outcome (Option PollPrepared)))

/-- The selected first packet gets decryption provenance when its
id matches the packet just published in this same original execution. -/
def PublicationPollObservation (pid : PeerId) (budget : Nat)
    (result : PublicationPollResult) : Prop :=
  result.1 = result.2.isSome ∧
    ∀ pub poll, result.2 = some (pub, poll) →
      PublishedAuthentication pub ∧ PollEndpointObservation pid budget pub.publication poll ∧
      ∀ cut atEndpoint, poll.2 = .ok (some (.endpoint cut), atEndpoint) →
        cut.id = pub.id → PollEndpointAuthentication pub cut

end Leanux.Proofs.WG.Roaming
