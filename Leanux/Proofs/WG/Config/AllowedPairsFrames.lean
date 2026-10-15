import Leanux.Proofs.WG.Config.AllowedPairsModel
import Leanux.Proofs.WG.Config.AllowedRemovalFrames

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

theorem deleteListedNodes_nodePairs (id : NodeId) (d : Device) (pairs : NodePairs d) :
    NodePairs (deleteListedNodes id d d.peers.toList) := by
  intro other n resident
  rw [deleteListedNodes_nodes] at resident
  exact pairs other n resident

end Leanux.Proofs.WG.Config
