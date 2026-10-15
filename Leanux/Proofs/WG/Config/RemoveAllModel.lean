import Leanux.Proofs.WG.Config.CollisionModel
import Leanux.Proofs.WG.Config.AllowedPairsModel
import Leanux.Proofs.WG.Campaign2.View

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

def ListedResidents (d : Device) (ids : List PeerId) : Prop :=
  ∀ pid ∈ ids, ∃ p, d.peers[pid]? = some p

/-- The first pass uses one fixed list and successive original removal states;
it never substitutes a sequence of complete peerRemove calls. -/
inductive DeadPassEffect : Device → List PeerId → Device → Prop
  | nil (d) : DeadPassEffect d [] d
  | cons (d : Device) (pid : PeerId) (rest : List PeerId) (p : Peer)
      (removed final : Device)
      (resident : d.peers[pid]? = some p)
      (removal : RemovalEffect (unlistPeer d pid) p.allowedipsList removed)
      (tail : DeadPassEffect (deadPeerDevice removed pid p) rest final) :
      DeadPassEffect d (pid :: rest) final

/-- Actual post-free device and the snapshot between the two removal passes. -/
structure RemoveAllCall where
  afterFree : Device
  afterMark : Campaign2.Snapshot

def RemoveAllFacts (cut : RemoveAllCall) : Prop :=
  NodePairs cut.afterFree → ListedResidents cut.afterFree cut.afterFree.peerList →
    ∃ marked, cut.afterMark.wg.device = some marked ∧
      DeadPassEffect cut.afterFree cut.afterFree.peerList marked ∧
      ∀ pid ∈ cut.afterFree.peerList, ∃ p, marked.peers[pid]? = some p ∧ p.isDead = true

end Leanux.Proofs.WG.Config
