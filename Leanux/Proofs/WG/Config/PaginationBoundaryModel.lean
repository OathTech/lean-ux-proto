import Leanux.Proofs.WG.Config.PaginationPlanModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

/-- Each boundary is fresh against every node already emitted. This permits
repeated IDs away from a boundary; it is precisely the lookup condition used by
the actual first-occurrence cursor search. -/
def ipv4TailBoundaryFresh (extra : Nat) (before : List NodeId) : List NodeId → Prop
  | [] => True
  | start :: rest => start ∉ before ∧
      ipv4TailBoundaryFresh extra (before ++ start :: rest.take extra) (rest.drop extra)
termination_by ids => ids.length
decreasing_by simp_wf; omega

def ipv4PaginationFresh (d : Device) : List NodeId → Prop
  | [] => True
  | first :: rest => ipv4TailBoundaryFresh (ipv4ResumeCapacity d - 1)
      (first :: rest.take (ipv4FirstCapacity d - 1))
      (rest.drop (ipv4FirstCapacity d - 1))

/-- The real callback value for one canonical resumed page. -/
def ipv4ResumeCall (d : Device) (p : Peer) (nodes : NodeId → AipNode)
    (start : NodeId) (rest : List NodeId) : DumpCall :=
  let front := start :: rest.take (ipv4ResumeCapacity d - 1)
  match rest.drop (ipv4ResumeCapacity d - 1) with
  | [] => socketLastCall d p nodes front
  | next :: _ => socketCallbackResult d
      {hasWg := true,nextAllowedip := some next,allowedipsSeq := d.peerAllowedips.seq}
      (NLMSG_GOODSIZE - devicePrefixSpace d - (44 + 28 * front.length))
      {suffixLast p nodes front with split := true} true

theorem ipv4Pagination_capacity (d : Device)
    (room : devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE) :
    0 < ipv4FirstCapacity d ∧
    devicePrefixSpace d + 140 + 28 * ipv4FirstCapacity d ≤ NLMSG_GOODSIZE ∧
    NLMSG_GOODSIZE < devicePrefixSpace d + 140 + 28 * (ipv4FirstCapacity d + 1) ∧
    0 < ipv4ResumeCapacity d ∧
    devicePrefixSpace d + 44 + 28 * ipv4ResumeCapacity d ≤ NLMSG_GOODSIZE ∧
    NLMSG_GOODSIZE < devicePrefixSpace d + 44 + 28 * (ipv4ResumeCapacity d + 1) := by
  unfold ipv4FirstCapacity ipv4ResumeCapacity
  omega

/-- Exact completed socket state, retaining the real room test that decides
whether DONE is inline or requires a later receive. -/
def paginationCompletedSocket (sock : NlSock) (call : DumpCall) : NlSock :=
  if call.skb.room < nlmsgTotal 4 then
    {sock with ctx := call.ctx,prevSeq := call.prevSeq,dumpDoneErrno := 0,queue := [call.skb]}
  else
    {sock with ctx := call.ctx,prevSeq := call.prevSeq,dumpDoneErrno := 0,cbRunning := false, queue := [{call.skb with room := call.skb.room - nlmsgTotal 4, messages := call.skb.messages ++ [NlMessage.done 2 0]}]}

/-- The exact receive count from a queued predecessor DATA through the final
resumed page, including the separate DONE receive when its DATA is full. -/
def ipv4TailReceiveCount (d : Device) : List NodeId → Nat
  | [] => 0
  | start :: rest =>
    match rest.drop (ipv4ResumeCapacity d - 1) with
    | [] => if NLMSG_GOODSIZE - (devicePrefixSpace d + 44 + 28 * (start :: rest).length) < 20
        then 3 else 2
    | _ :: _ => 1 + ipv4TailReceiveCount d (rest.drop (ipv4ResumeCapacity d - 1))
termination_by ids => ids.length
decreasing_by simp_wf; omega


end Leanux.Proofs.WG.Config
