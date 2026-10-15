import Leanux.Proofs.WG.Config.EmptyKeypairs
import Leanux.Proofs.WG.Index.ReleaseModel

/-! Pure ordered state transformations for quiet timer and peer cleanup. -/
set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def deleteTimersPeer : List PeerTimer → Peer → Peer
  | [], p => p
  | t :: ts, p => deleteTimersPeer ts (p.setTimer t none)

def deleteTimersDevice : List PeerTimer → Device → PeerId → Peer → Device
  | [], d, _, _ => d
  | t :: ts, d, pid, p =>
    deleteTimersDevice ts (withPeer d pid (p.setTimer t none)) pid (p.setTimer t none)

def quietCleanupPeer (p : Peer) : Peer := deleteTimersPeer PeerTimer.all (emptyKeysPeer p)

def quietCleanupDevice (d : Device) (pid : PeerId) (p : Peer) : Device :=
  deleteTimersDevice PeerTimer.all (emptyKeysDevice d pid p) pid (emptyKeysPeer p)

def quietRemovedDevice (d : Device) (pid : PeerId) (p : Peer) : Device :=
  let cleaned := quietCleanupDevice d pid p
  Index.releasedPeerDevice { cleaned with numPeers := cleaned.numPeers - 1 } pid (quietCleanupPeer p)

end Leanux.Proofs.WG.Config
