import Leanux.WG.Types

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

namespace ConfirmationReinstallWitness

def peer : Peer := {
  remoteStatic := [], presharedKey := [], precomputedStaticStatic := [], internalId := 0,
  keypairNext := some 0 }
def key : Keypair := { internalId := 17, peer := some 0, iAmTheInitiator := false }
def device : Device := {
  ifindex := 0, ifname := "wg0", numPeers := 1, peerList := [0],
  peers := ({} : Std.TreeMap PeerId Peer).insert 0 peer,
  keypairs := ({} : Std.TreeMap KeypairId Keypair).insert 0 key,
  nextKeypairId := 1 }

end ConfirmationReinstallWitness
open ConfirmationReinstallWitness

/-- The arbitrary entry contains a single positively referenced responder key, initially in next. -/
theorem confirmationReinstallWitness_shape :
    device.peers[0]? = some peer ∧ device.keypairs[0]? = some key ∧
    peer.keypairPrevious = none ∧ peer.keypairCurrent = none ∧
    peer.keypairNext = some 0 ∧ key.refcount = 1 ∧ key.internalId = 17 := by
  simp [device, peer, key]


end Leanux.Proofs.WG.Noise
