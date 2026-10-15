import Leanux.Proofs.WG.Config.DeviceDump

set_option pp.structureInstances false
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

def singlePeerJson (d : Device) (p : Peer) : Json :=
  Json.mkObj (deviceFixedAttrs d ++ [("peers", Json.arr #[Json.mkObj
    (peerFixedAttrs p ++ [("allowed_ips", Json.arr #[])])])])

theorem deviceFixedAttrs_nonempty (d : Device) : (deviceFixedAttrs d).isEmpty = false := by
  simp [deviceFixedAttrs]

theorem peerFixedAttrs_no_ips (p : Peer) :
    (peerFixedAttrs p).any (·.1 == "allowed_ips") = false := by
  cases he : p.endpoint <;> simp [peerFixedAttrs, he]

theorem coalesce_single (d : Device) (p : Peer) :
    coalesce ((singlePeerDump d p).skb.messages ++ [.done 2 0]) = pure (.ok (singlePeerJson d p)) := by
  have hn : deviceFixedAttrs d ≠ [] := by simp [deviceFixedAttrs]
  simp [singlePeerDump, coalesce, hn, List.forIn_cons, List.forIn_nil, bind_assoc,
    deviceFixedAttrs_nonempty, peerFixedAttrs_no_ips, singlePeerJson]

end Leanux.Proofs.WG.Config
