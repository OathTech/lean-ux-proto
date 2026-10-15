import Leanux.Proofs.WG.Config.RemoveFlagSource
import Leanux.Proofs.WG.Config.KeyRequest

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- One peer command, selected by device index, without other device updates. -/
def singlePeerAttrs (d : Device) (a : PeerAttrs) : DeviceAttrs :=
  { device := byIndex d, peers := some [.attrs a] }

theorem setDevice_remove_flag (a : PeerAttrs) (key : Key) (flags : UInt32)
    (pid : PeerId) (d : Device) (p : Peer)
    (pubkey : a.publicKey = some key) (flagattr : a.flags = some flags)
    (valid : flags &&& ~~~WGPEER_F_ALL = 0)
    (protocol : a.protocolVersion = none ∨ a.protocolVersion = some 1)
    (remove : flags &&& WGPEER_F_REMOVE_ME ≠ 0)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (pairs : NodePairs d)
    (live : 0 < p.refcount) (bounded : p.refcount + 1 < 2 ^ 31)
    (count : 0 < d.numPeers) (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = []) :
    Ensures (wgSetDevice (singlePeerAttrs d a))
      (fun w => w.k.wg = some d ∧ selectsDevice w d)
      (fun ret w => ret = 0 ∧ ∃ final, w.k.wg = some final ∧
        RemoveFlagEffect pid (requestGeneration d) p final) := by
  have hl := lookupInterface_index d
  have hp := (ensures_iff _ _ _).mp
    (setPeer_remove_flag a key flags pid (requestGeneration d) p pubkey flagattr valid protocol
      remove found resident pairs live bounded count send clear)
  have peers : Ensures (devicePeersSource (singlePeerAttrs d a))
      (fun w => w.k.wg = some (requestGeneration d))
      (fun ret w => ret = 0 ∧ ∃ final, w.k.wg = some final ∧
        RemoveFlagEffect pid (requestGeneration d) p final) := by
    rw [ensures_iff]
    simp [devicePeersSource, singlePeerAttrs, List.forIn_cons, List.forIn_nil]
    mvcgen [branch, hp]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all
  have hpeers := (ensures_iff _ _ _).mp peers
  clear hp peers
  rw [← wgSetDevice_source, ensures_iff]
  simp only [wgSetDeviceSource, deviceUpdateSource, deviceKeySource, singlePeerAttrs]
  mvcgen [WG.orM, WG.andM, branch, modifyDev, modifyK, invariant, hl, hpeers]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [requestGeneration, WGDEVICE_F_ALL, WGDEVICE_F_REPLACE_PEERS]
  all_goals first | exact hpeers _ (by simp_all [requestGeneration]) | grind only

end Leanux.Proofs.WG.Config
