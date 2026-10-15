import Leanux.Proofs.WG.Config.ReplacementConverseSource
import Leanux.Proofs.WG.Config.KeyRequest

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem setDevice_replace_effect_pairs (key : Key) (pid : PeerId) (d : Device) (p : Peer)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (pairs : NodePairs d)
    (live : 0 < p.refcount) (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false) :
    Ensures (wgSetDevice (replaceAllowedipsDeviceAttrs d key))
      (fun w => w.k.wg = some d ∧ selectsDevice w d)
      (fun ret w => ret = 0 ∧ ∃ removed,
        RemovalEffect (withPeer (requestGeneration d) pid { p with refcount := p.refcount + 1 })
          p.allowedipsList removed ∧
        w.k.wg = some (generalReplacementDevice removed pid p)) := by
  have hl := lookupInterface_index d
  have hp := (ensures_iff _ _ _).mp
    (setPeer_replace_effect_pairs key pid (requestGeneration d) p
      found resident pairs live bounded down)
  have peers : Ensures (devicePeersSource (replaceAllowedipsDeviceAttrs d key))
      (fun w => w.k.wg = some (requestGeneration d))
      (fun ret w => ret = 0 ∧ ∃ removed,
        RemovalEffect (withPeer (requestGeneration d) pid { p with refcount := p.refcount + 1 })
          p.allowedipsList removed ∧
        w.k.wg = some (generalReplacementDevice removed pid p)) := by
    rw [ensures_iff]
    simp [devicePeersSource, replaceAllowedipsDeviceAttrs, List.forIn_cons, List.forIn_nil]
    mvcgen [branch, hp]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all
  have hpeers := (ensures_iff _ _ _).mp peers
  clear hp peers
  rw [← wgSetDevice_source, ensures_iff]
  simp only [wgSetDeviceSource, deviceUpdateSource, deviceKeySource, replaceAllowedipsDeviceAttrs]
  mvcgen [WG.orM, WG.andM, branch, modifyDev, modifyK, invariant, hl, hpeers]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [requestGeneration, WGDEVICE_F_ALL, WGDEVICE_F_REPLACE_PEERS]
  all_goals first | exact hpeers _ (by simp_all [requestGeneration]) | grind only

end Leanux.Proofs.WG.Config
