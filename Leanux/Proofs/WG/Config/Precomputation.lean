import Leanux.Proofs.WG.Config.PrivateKey

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def precomputeDevice (d : Device) (pid : PeerId) (p : Peer) : Device :=
  let out := curve25519 d.staticIdentity.staticPrivate p.remoteStatic
  if d.staticIdentity.hasIdentity then
    let wrote := withPeer d pid { p with precomputedStaticStatic := out.1 }
    if out.2 then wrote
    else withPeer wrote pid { p with precomputedStaticStatic := List.replicate 32 0 }
  else withPeer d pid { p with precomputedStaticStatic := List.replicate 32 0 }

theorem precomputeStaticStatic_returns (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Returns (precomputeStaticStatic pid) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some (precomputeDevice d pid p)) := by
  rw [returns_iff]
  mvcgen [precomputeStaticStatic, requireNotPending, getPeer, getDev, getK,
    setPeer, modifyDev, modifyK, branch, invariant, unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [precomputeDevice, withPeer]
  all_goals subst_vars
  all_goals simp_all [precomputeDevice, withPeer]
  all_goals grind only

theorem precomputeDevice_peer (pid : PeerId) (d : Device) (p : Peer) :
    (precomputeDevice d pid p).peers[pid]? =
      some { p with precomputedStaticStatic := precomputedAfter d.staticIdentity p } := by
  simp only [precomputeDevice, precomputedAfter]
  split <;> simp_all [withPeer]
  split <;> simp_all [withPeer]


end Leanux.Proofs.WG.Config
