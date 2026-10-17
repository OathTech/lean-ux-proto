import Leanux.WG.Types

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

def responseTagMap (device : Option Device) (pid : PeerId) : Option Nat :=
  (device.bind fun d => d.peers[pid]?).map Peer.handshakeState


end Leanux.Proofs.WG.Noise
