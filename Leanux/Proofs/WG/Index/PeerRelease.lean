import Leanux.Proofs.WG.Index.Release
import Leanux.Proofs.WG.Index.PeerReleaseEffects
import Leanux.Proofs.WG.Index.ReleaseBounds

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

theorem peerPut_exact (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount) :
    Returns (peerPut (some pid)) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some (releasedPeerDevice d pid p)) := by
  rw [returns_iff]
  by_cases last : p.refcount = 1
  all_goals noise_vcgen [peerPut, requireNotPending, refcountDecAndTest,
    getPeer, getDev, getK, setPeer, modifyDev, modifyK,
    branch, branchCmp, invariant, unsupported, retirePeerUnits, indexRemove,
    _private.Leanux.WG.Peer.«0».Leanux.WG.unhashEntry]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all only [Option.map_some, Option.some.injEq]
  all_goals subst_vars
  all_goals simp_all [releasedPeerDevice, removeOwner]
  all_goals grind only

end Leanux.Proofs.WG.Index
