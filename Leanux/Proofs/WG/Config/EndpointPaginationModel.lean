import Leanux.Proofs.WG.Config.PaginationCountModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- Actual first-page capacity, including the complete endpoint attribute. -/
def endpointFirstCapacity (d : Device) (p : Peer) : Nat :=
  (NLMSG_GOODSIZE - devicePrefixSpace d - (peerFixedSpace p + 4)) / 28

/-- Only the first boundary changes; all resumed capacities are unchanged. -/
def endpointPaginationFresh (d : Device) (p : Peer) : List NodeId → Prop
  | [] => True
  | first :: rest => ipv4TailBoundaryFresh (ipv4ResumeCapacity d - 1)
      (first :: rest.take (endpointFirstCapacity d p - 1))
      (rest.drop (endpointFirstCapacity d p - 1))

/-- Exact DATA plus DONE receive count on the first-page progress domain. -/
def endpointPaginationReceiveCount (d : Device) (p : Peer) : List NodeId → Nat
  | [] => 1
  | first :: rest =>
    if (first :: rest).length ≤ endpointFirstCapacity d p then
      if NLMSG_GOODSIZE - (devicePrefixSpace d + (peerFixedSpace p + 4) + 28 * (first :: rest).length) < 20
      then 2 else 1
    else ipv4TailReceiveCount d (rest.drop (endpointFirstCapacity d p - 1))

/-- The actual first partial DATA callback; endpoint bytes affect its room. -/
def endpointFirstCall (d : Device) (p : Peer) (nodes : NodeId → AipNode)
    (front : List NodeId) (next : NodeId) : DumpCall :=
  socketCallbackResult d
    {hasWg := true,nextAllowedip := some next,allowedipsSeq := d.peerAllowedips.seq}
    (NLMSG_GOODSIZE - (devicePrefixSpace d + (peerFixedSpace p + 4) + 28 * front.length))
    (socketFirstPeer p nodes front) true

theorem endpointFirstCapacity_bounds (d : Device) (p : Peer)
    (room : devicePrefixSpace d + max 168 (peerFixedSpace p + 32) ≤ NLMSG_GOODSIZE) :
    devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE ∧
    0 < endpointFirstCapacity d p ∧
    devicePrefixSpace d + (peerFixedSpace p + 4) + 28 * endpointFirstCapacity d p ≤ NLMSG_GOODSIZE ∧
    NLMSG_GOODSIZE < devicePrefixSpace d + (peerFixedSpace p + 4) + 28 * (endpointFirstCapacity d p + 1) := by
  unfold endpointFirstCapacity
  omega

/-- The endpoint-aware data calculations specialize exactly to the existing
no-endpoint calculations; existing theorem signatures need not change. -/
theorem endpointPagination_none (d : Device) (p : Peer) (endpoint : p.endpoint = none) :
    endpointFirstCapacity d p = ipv4FirstCapacity d ∧
    ∀ ids, (endpointPaginationFresh d p ids ↔ ipv4PaginationFresh d ids) ∧
      endpointPaginationReceiveCount d p ids = ipv4PaginationReceiveCount d ids := by
  have capacity : endpointFirstCapacity d p = ipv4FirstCapacity d := by
    simp [endpointFirstCapacity,ipv4FirstCapacity,peerFixedSpace,endpoint,AF_INET,AF_INET6]
  refine ⟨capacity,?_⟩
  intro ids
  cases ids <;> simp [endpointPaginationFresh,ipv4PaginationFresh,
    endpointPaginationReceiveCount,ipv4PaginationReceiveCount,capacity,peerFixedSpace,endpoint,AF_INET,AF_INET6]
end Leanux.Proofs.WG.Config
