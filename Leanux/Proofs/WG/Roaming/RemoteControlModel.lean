import Leanux.Proofs.WG.Roaming.RemoteRetentionModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteControl
open Leanux Leanux.WG

def setterRemotes (entry : RemoteMap) (pid : PeerId) (endpoint : Endpoint) : RemoteMap :=
  if endpoint.family = AF_INET ∨ endpoint.family = AF_INET6 then
    updateRemote entry pid (destination endpoint) else entry

end Leanux.Proofs.WG.Roaming.RemoteControl
