import Leanux.Proofs.WG.Config.PeerScalars

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def clearedSource (p : Peer) (reset : UInt64) : Peer :=
  { p with
    endpoint := p.endpoint.map fun e => { e with src := 0, srcIf := 0 }
    dstCache := { p.dstCache with resetTs := reset, slot := none } }

theorem clearEndpointSource_exact (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (clearPeerEndpointSrc pid) (fun w => w.k.wg = some d)
      (fun _ w => ∃ d' reset, w.k.wg = some d' ∧
        d' = { d with peers := d'.peers } ∧
        d'.peers[pid]? = some (clearedSource p reset) ∧
        ∀ q, q ≠ pid → d'.peers[q]? = d.peers[q]?) := by
  let p1 : Peer := { p with endpoint := p.endpoint.map fun (e : Endpoint) => { e with src := 0, srcIf := 0 } }
  let d1 := withPeer d pid p1
  have hh := Roaming.hiddenJiffies_kernel_spec (fun k => k.wg = some d1)
  rw [ensures_iff]
  mvcgen [clearPeerEndpointSrc, dstCacheResetNow, dstCacheReset,
    getPeer, getDev, getK, setPeer, modifyDev, modifyK, invariant, hh]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [clearedSource, d1, p1, withPeer]
  all_goals grind

end Leanux.Proofs.WG.Config
