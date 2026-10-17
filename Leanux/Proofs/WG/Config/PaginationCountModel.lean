import Leanux.Proofs.WG.Config.PaginationBoundaryModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

/-- The actual number of receive envelopes for the single-peer, endpoint-none
IPv4 getter domain. Empty allowed IPs emit fixed peer DATA with inline DONE
under the header-room bound. A fitting nonempty page needs one or two receives
according to its remaining room; multi-page dumps use the canonical resumed
count, which includes the queued first DATA and any separate DONE. -/
def ipv4PaginationReceiveCount (d : Device) : List NodeId → Nat
  | [] => 1
  | first :: rest =>
    if (first :: rest).length ≤ ipv4FirstCapacity d then
      if NLMSG_GOODSIZE - (devicePrefixSpace d + 140 + 28 * (first :: rest).length) < 20
      then 2 else 1
    else ipv4TailReceiveCount d (rest.drop (ipv4FirstCapacity d - 1))

end Leanux.Proofs.WG.Config
