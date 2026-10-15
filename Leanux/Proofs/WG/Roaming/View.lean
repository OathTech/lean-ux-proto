import Leanux.Proofs.WG.Campaign2.View
import Leanux.Proofs.WG.Roaming.Model

namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG

def remoteAt (s : Campaign2.Snapshot) (pid : PeerId) : Option (Nat × Nat × Nat × Nat) :=
  ((s.peerAt pid).bind Peer.endpoint).map destination

end Leanux.Proofs.WG.Roaming
