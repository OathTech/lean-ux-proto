import Leanux.Proofs.WG.Campaign2.ProductView
import Leanux.WG.RxData

/-! The observation is taken before the interrupt-exit callback. A later
callback may consume the packet or change the device. -/
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG

def packetAt (s : Campaign2.Product.Snapshot) (id : SkbId) : Option RxPacket :=
  s.wg.device.bind fun d => d.rxSkbs[id]?

def keyAt (s : Campaign2.Product.Snapshot) (id : KeypairId) : Option Keypair :=
  s.wg.device.bind fun d => d.keypairs[id]?

structure PublicationCut where
  afterSoftirq : Campaign2.Product.Snapshot
  beforeDecrypt : Campaign2.Product.Snapshot
  id : SkbId
  owner : PeerId
  input : RxPacket
  decrypted : Option RxPacket
  publication : Campaign2.Product.Snapshot

def PublishedAuthentication (cut : PublicationCut) : Prop :=
  (∃ d ring, cut.afterSoftirq.wg.device = some d ∧
    d.decryptQueue.consume = (some cut.id, ring)) ∧
  packetAt cut.afterSoftirq cut.id = some cut.input ∧
  packetAt cut.beforeDecrypt cut.id = some cut.input ∧
  ∃ published,
    packetAt cut.publication cut.id = some published ∧
    published.state = (if cut.decrypted.isSome then .crypted else .dead) ∧
    (published.state = .crypted → ∃ key,
      keyAt cut.beforeDecrypt cut.input.keypair = some key ∧
      published.source = cut.input.source ∧
      published.peer = cut.input.peer ∧
      published.keypair = cut.input.keypair ∧
      published.nonce = u64le cut.input.bytes 8 ∧
      aeadDecrypt key.receiving.key (counterNonce (u64le cut.input.bytes 8))
        (cut.input.bytes.drop 16) [] = some published.bytes)

/-- A normal full step has a matching successful prefix observation. No
packet or device condition is imposed on the final callback-modified state. -/
def PublicationObservation
    (result : Bool × Campaign2.Product.Outcome (Option PublicationCut)) : Prop :=
  ∃ found atCut,
    result.2 = .ok (found, atCut) ∧ result.1 = found.isSome ∧
    ∀ cut, found = some cut →
      cut.publication = atCut ∧ PublishedAuthentication cut

end Leanux.Proofs.WG.Roaming
