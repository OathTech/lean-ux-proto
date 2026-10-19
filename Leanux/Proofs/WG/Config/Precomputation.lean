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

def precomputeAmbient (d : Device) (p : Peer) (ambient : Ambient) : Ambient :=
  let mark (a : Ambient) (site : Decision) (value : Bool) :=
    {a with steps := a.steps.push {decision := site, outcome := value, netRx := a.netRxSection}}
  let first := mark ambient .precomputeNoIdentity (!d.staticIdentity.hasIdentity)
  if d.staticIdentity.hasIdentity then
    mark first .precomputeNullPoint (!(curve25519 d.staticIdentity.staticPrivate p.remoteStatic).2)
  else first
theorem precomputeStaticStatic_run (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (g : WGWorld) (ambient : Ambient)
    (device : g.dev = some d) :
    ((precomputeStaticStatic pid).run g).run ambient =
      .ok (((),{g with dev:=some (precomputeDevice d pid p)}),precomputeAmbient d p ambient) := by
  cases has : d.staticIdentity.hasIdentity
  all_goals cases nonNull : (curve25519 d.staticIdentity.staticPrivate p.remoteStatic).2
  all_goals simp [precomputeStaticStatic,requireNotPending,getPeer,getDev,device,resident,
    setPeer,modifyDev,branch,AmbientM.branch,has,nonNull,precomputeDevice,withPeer,precomputeAmbient]
  all_goals rfl
theorem precomputeStaticStatic_returns (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Returns (precomputeStaticStatic pid) (fun g => g.dev = some d)
      (fun _ g => g.dev = some (precomputeDevice d pid p)) := by
  intro g ambient device
  exact ⟨(),{g with dev:=some (precomputeDevice d pid p)},precomputeAmbient d p ambient,
    precomputeStaticStatic_run pid d p resident g ambient device,rfl⟩
theorem precomputeDevice_peer (pid : PeerId) (d : Device) (p : Peer) :
    (precomputeDevice d pid p).peers[pid]? =
      some { p with precomputedStaticStatic := precomputedAfter d.staticIdentity p } := by
  simp only [precomputeDevice, precomputedAfter]
  split <;> simp_all [withPeer]
  split <;> simp_all


end Leanux.Proofs.WG.Config
