import Leanux.Proofs.WG.Roaming.PollEndpointModel

namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG

structure NapiFirstCut where
  pid : PeerId
  entry : Campaign2.Product.Snapshot
  poll : Campaign2.Product.Outcome (Option PollPrepared)

def queueHead (entry : Campaign2.Product.Snapshot) (pid : PeerId) : Option SkbId :=
  entry.wg.device.bind fun d => (d.peers[pid]?).bind fun p => p.rxQueue.all.head?

def OwnerScheduled (entry : Campaign2.Product.Snapshot) (pid : PeerId) : Prop :=
  ∃ d p, entry.wg.device = some d ∧ d.peers[pid]? = some p ∧ p.napiScheduled = true

def NapiFirstFacts (pending : Option (List PeerId)) (entry : Campaign2.Product.Snapshot)
    (result : Option NapiFirstCut) : Prop :=
  ∀ cut, result = some cut → cut.entry = entry ∧ pending.bind List.head? = some cut.pid ∧
    ∀ endpoint atEndpoint, cut.poll = .ok (some (.endpoint endpoint),atEndpoint) →
      PollEndpointFacts cut.pid entry endpoint ∧ queueHead entry cut.pid = some endpoint.id

def NapiOwnerFacts (entry : Campaign2.Product.Snapshot) (owner : PeerId)
    (result : Option NapiFirstCut) : Prop :=
  ∀ cut, result = some cut → cut.pid = owner ∧ cut.entry.wg = entry.wg ∧
    ∀ endpoint atEndpoint, cut.poll = .ok (some (.endpoint endpoint),atEndpoint) →
      PollEndpointFacts owner entry endpoint ∧ queueHead entry owner = some endpoint.id

/-- The actual publication and pre-put NAPI poll are linked through the
published owner's queue. This concerns the first setter cut, not final state. -/
def NativePublicationOwnerObservation
    (result : Bool × Option (PublicationCut × Option NapiFirstCut)) : Prop :=
  result.1 = result.2.isSome ∧
  ∀ pub first, result.2 = some (pub,first) →
    PublishedAuthentication pub ∧ OwnerScheduled pub.publication pub.owner ∧
    NapiOwnerFacts pub.publication pub.owner first ∧
    ∀ cut, first = some cut → ∀ endpoint atEndpoint,
      cut.poll = .ok (some (.endpoint endpoint),atEndpoint) →
      queueHead pub.publication pub.owner = some pub.id →
      endpoint.id = pub.id ∧ PollEndpointAuthentication pub endpoint


end Leanux.Proofs.WG.Roaming
