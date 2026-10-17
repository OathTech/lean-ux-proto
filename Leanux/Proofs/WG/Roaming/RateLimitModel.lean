import Leanux.WG.Receive
import Leanux.Proofs.WG.Campaign2.ProductView
import Leanux.Proofs.WG.Roaming.View

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG

/-- A normal full call supplies a successful actual strict-prefix observation.
Only a rate-limit verdict implies peer-map preservation here: noCookie alone
may admit a handshake when the receiver is not under load. -/
def RateLimitRejectionObservation (entry : Campaign2.Product.Snapshot)
    (receipt : Campaign2.Product.Outcome (Bool × MacState))
    (final : Campaign2.Product.Snapshot) : Prop :=
  ∃ loaded mac atCut, receipt = .ok ((loaded, mac), atCut) ∧
    (mac = .ratelimited →
      final.wg.device.map (·.peers) = entry.wg.device.map (·.peers) ∧
      ∀ pid, remoteAt final.toSnapshot pid = remoteAt entry.toSnapshot pid)

end Leanux.Proofs.WG.Roaming
