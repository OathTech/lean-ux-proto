import Leanux.Proofs.WG.Config.WeightedPaginationModel
import Leanux.Proofs.WG.Config.PaginationBoundaryModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- The actual first DATA callback. An empty input has no allowed-IP nest or
raw attribute. A nonempty input has that nest even when its fitting prefix is
empty; endpoint fields retain their original serializer and byte accounting. -/
def mixedFirstCall (d : Device) (p : Peer) (nodes : NodeId → AipNode) : List NodeId → DumpCall
  | [] => socketCallbackResult d {hasWg := true}
      (NLMSG_GOODSIZE - devicePrefixSpace d - peerFixedSpace p)
      {publicKey := hexKey p.remoteStatic, attrs := peerFixedAttrs p} false
  | first :: rest =>
    let result := weightedPrefix nodes
      (NLMSG_GOODSIZE - devicePrefixSpace d - (peerFixedSpace p + 4)) (first :: rest)
    let ctx : DumpCtx := match result.2 with
      | [] => {hasWg := true}
      | next :: _ => {hasWg := true, nextAllowedip := some next, allowedipsSeq := d.peerAllowedips.seq}
    socketCallbackResult d ctx
      (NLMSG_GOODSIZE - (devicePrefixSpace d + (peerFixedSpace p + 4) + dumpNodesSpace nodes result.1))
      {publicKey := hexKey p.remoteStatic,
       attrs := peerFixedAttrs p ++ [("allowed_ips", Json.arr (dumpNodeJsons nodes result.1))],
       split := !result.2.isEmpty} (!result.2.isEmpty)

/-- Exact socket after the original start, including the actual inline-DONE
versus separate-DONE test when the first callback completes. -/
def mixedStartedSocket (sock : NlSock) (call : DumpCall) : NlSock :=
  let started := {sock with cbRunning := true, dumpDoneErrno := INT_MAX, prevSeq := 0, ctx := {hasWg := true}}
  if call.ret = 0 then paginationCompletedSocket started call
  else paginationMoreSocket started call

/-- Every first callback model has a NULL peer cursor, the current generation,
and a nonnegative return. This does not by itself assert callback execution. -/
theorem mixedFirstCall_shape (d : Device) (p : Peer) (nodes : NodeId → AipNode)
    (ids : List NodeId) :
    (mixedFirstCall d p nodes ids).ctx.nextPeer = none ∧
    (mixedFirstCall d p nodes ids).prevSeq = d.deviceUpdateGen ∧
    0 ≤ (mixedFirstCall d p nodes ids).ret := by
  cases ids with
  | nil => simp [mixedFirstCall, socketCallbackResult]
  | cons first rest =>
    unfold mixedFirstCall
    cases plan : weightedPrefix nodes
      (NLMSG_GOODSIZE - devicePrefixSpace d - (peerFixedSpace p + 4)) (first :: rest) with
    | mk front remaining =>
      cases remaining <;> simp [plan, socketCallbackResult]

end Leanux.Proofs.WG.Config
