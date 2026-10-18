import Leanux.Proofs.WG.AllowedIps.ClearEndpoint
import Leanux.Proofs.WG.Config.RemoveAllEffects

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

/-- Actual allowed-IP clearing retains node shape and listed residency, with
the same saved peer list. No distinctness of that list is assumed. -/
theorem cleared_removeAll_inputs (d out : Device) (hc : AllowedIps.Cleared d out)
    (pairs : NodePairs d) (listed : ListedResidents d d.peerList) :
    NodePairs out ∧ ListedResidents out out.peerList ∧ out.peerList = d.peerList := by
  have listEq : out.peerList = d.peerList := by
    have h := congrArg Device.peerList hc.frame
    exact h
  refine ⟨fun id n hn => pairs id n (hc.nodes id n hn), ?_, listEq⟩
  intro pid member
  obtain ⟨p, hp⟩ := listed pid (listEq ▸ member)
  exact ⟨{p with allowedipsList := []}, by rw [hc.peers, hp]; rfl⟩

end Leanux.Proofs.WG.Config
