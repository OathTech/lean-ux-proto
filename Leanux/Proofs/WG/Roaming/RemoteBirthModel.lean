import Leanux.Proofs.WG.Noise.DriverTagModel
import Leanux.Proofs.WG.Roaming.RemoteRetentionModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteBirth
open Leanux Leanux.WG Noise Lifetimes

def birthRemotes (before : RemoteMap) : Except Int PeerId → RemoteMap
  | .error _ => before
  | .ok pid => fun target => if pid = target then none else before target

def BirthRemoteEffect (r : PeerCreateReceipt) : Prop :=
  peerStampStore r.after = (match r.result with
    | .error _ => peerStampStore r.before
    | .ok pid => (peerStampStore r.before).allocate pid) ∧
  remoteMap r.after = birthRemotes (remoteMap r.before) r.result

end Leanux.Proofs.WG.Roaming.RemoteBirth
