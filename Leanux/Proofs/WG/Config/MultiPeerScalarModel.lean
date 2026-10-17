import Leanux.WG.Types

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

/-- The selected scalar write is visible at every duplicate list occurrence;
all other peer values are unchanged. -/
def scalarPeerView (peers : PeerId → Peer) (pid : PeerId) (psk : Key) (interval : Nat)
    (q : PeerId) : Peer :=
  if q = pid then {peers pid with presharedKey := psk,persistentKeepaliveInterval := interval}
  else peers q


end Leanux.Proofs.WG.Config
