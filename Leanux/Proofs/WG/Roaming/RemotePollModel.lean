import Leanux.Proofs.WG.Queues.RxPollHistory
import Leanux.Proofs.WG.Roaming.RemoteOriginModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemotePoll
open Leanux Leanux.WG Queues

/-- The completed data caller's actual endpoint argument. Its initialized
authentication and packet-source correspondence are derived separately from
the exact RX history, rather than assumed by this event classification. -/
def rxCause : RxHistory.Event → PeerId → Nat × Nat × Nat × Nat → Prop
  | .consumed _ _ _ r, pid, remote =>
    r.peer = pid ∧ destination r.endpoint = remote ∧
      (r.endpoint.family = AF_INET ∨ r.endpoint.family = AF_INET6)
  | _, _, _ => False

end Leanux.Proofs.WG.Roaming.RemotePoll
