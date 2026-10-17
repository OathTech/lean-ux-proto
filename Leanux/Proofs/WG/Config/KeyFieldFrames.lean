import Leanux.Proofs.WG.Config.ExpiryEffects

/-! Existing preservation support, separated from state-changing effects. -/
set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem precomputeDevice_other (pid q : PeerId) (d : Device) (p : Peer) (other : q ≠ pid) :
    (precomputeDevice d pid p).peers[q]? = d.peers[q]? := by
  simp only [precomputeDevice]
  split <;> simp_all [withPeer, Std.TreeMap.getElem?_insert, Ne.symm other]
  split <;> simp_all [Std.TreeMap.getElem?_insert, Ne.symm other]

theorem invalidateDevice_peers (d : Device) (kp : Option KeypairId) :
    (invalidateDevice d kp).peers = d.peers := by
  cases kp with
  | none => rfl
  | some id => cases found : d.keypairs[id]? <;> simp [invalidateDevice, found]

end Leanux.Proofs.WG.Config
