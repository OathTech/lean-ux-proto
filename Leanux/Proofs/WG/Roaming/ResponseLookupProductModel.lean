import Leanux.Proofs.WG.Roaming.ResponseConsumeProductModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.Product
open Leanux Leanux.WG

structure ResponseLookupRead where
  before : Campaign2.Product.Snapshot
  observed : Campaign2.Product.Outcome (Option (IndexOwner × PeerId))
  entry : Option (IndexOwner × PeerId)
  after : Campaign2.Product.Snapshot

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

/-- Extend observations only, using the actual fixture preserved by the native lift. -/
def restoreResponseLookupRead (fixture : Campaign2.Product.Fixture) (read : Roaming.ResponseLookupRead) :
    ResponseLookupRead where
  before := { toSnapshot := read.before, fixture }
  observed := read.observed.map fun (out, state) => (out, { toSnapshot := state, fixture })
  entry := read.entry
  after := { toSnapshot := read.after, fixture }

def restoreResponseLookupCut (fixture : Campaign2.Product.Fixture) (cut : Roaming.ResponseLookupCut) :
    ResponseLookupCut := ⟨cut.input, restoreResponseLookupRead fixture cut.lookup⟩

end Leanux.Proofs.WG.Roaming.Product
