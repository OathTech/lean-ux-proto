import Leanux.Proofs.WG.Roaming.ResponseCallProductModel
import Leanux.Proofs.WG.Campaign2.Bridge
import Leanux.Proofs.WG.Roaming.View

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG

/-- The MAC verdict which admits a handshake to its consumer. -/
def responseMacAdmitted (loaded : Bool) (mac : MacState) : Prop :=
  (loaded = true ∧ mac = .withCookie) ∨ (loaded = false ∧ mac = .noCookie)

def ResponseRejectionObservation (entry : Campaign2.Product.Snapshot)
    (receipt : Campaign2.Product.Outcome (Bool × MacState) ×
      Campaign2.Product.Outcome (Option Product.ResponseCallCut))
    (final : Campaign2.Product.Snapshot) : Prop :=
  ∃ loaded mac atMac cut atCut,
    receipt = (.ok ((loaded,mac),atMac), .ok (cut,atCut)) ∧
      (responseMacAdmitted loaded mac → cut = none →
        ∀pid, remoteAt final.toSnapshot pid = remoteAt entry.toSnapshot pid)

end Leanux.Proofs.WG.Roaming
