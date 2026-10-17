import Leanux.Proofs.WG.Campaign2.View

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

/-- Data-only allocation cursor and tracked optional next slot. Neither a
resident key nor initialization history is assumed. -/
def freshInstallView (tracked : PeerId) (device : Option Device) :
    Option Nat × Option (Option KeypairId) :=
  (device.map Device.nextKeypairId,
    (device.bind fun d => d.peers[tracked]?).map Peer.keypairNext)

/-- The initial pending identity precedes the current allocation cursor.
This explicit local premise is not inferred from a store-residency invariant. -/
def FreshNextBound (tracked : PeerId) (s : Campaign2.Snapshot) : Prop :=
  ∀ d p id, s.wg.device = some d → d.peers[tracked]? = some p →
    p.keypairNext = some id → id < d.nextKeypairId


end Leanux.Proofs.WG.Noise
