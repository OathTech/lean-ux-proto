import Leanux.Proofs.WG.Config.PaginationCoalesceModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- The actual coalescer merges an adjacent continuation before processing
the unchanged remainder, including any later error. -/
theorem coalesce_merge_continuation_endpoint (d : Device) (p : Peer) (nodes : NodeId → AipNode)
    (front ids : List NodeId) (more : Bool) (tail : List NlMessage)
    :
    coalesce (.data 2 (deviceFixedAttrs d) (some [socketFirstPeer p nodes front]) ::
      .data 2 (deviceFixedAttrs d) (some [{suffixLast p nodes ids with split := more}]) :: tail) =
    coalesce (.data 2 (deviceFixedAttrs d)
      (some [{socketFirstPeer p nodes (front ++ ids) with split := more}]) :: tail) := by
  have nonempty : deviceFixedAttrs d ≠ [] := by simp [deviceFixedAttrs]
  cases endpoint : p.endpoint <;> simp [coalesce,socketFirstPeer,suffixLast,peerFixedAttrs,endpoint,nonempty,
    List.forIn_cons,List.forIn_nil,List.lookup,ipv4Jsons,ipv4NodeJson]

/-- Coalescing any finite page sequence preserves every allowed-IP occurrence
in order. Envelope boundaries and repeated entries do not alter the JSON. -/
theorem coalesce_pagination_endpoint (d : Device) (p : Peer) (nodes : NodeId → AipNode)
    (front : List NodeId) (rest : List (List NodeId)) :
    coalesce (paginationMessages d p nodes front rest) =
      pure (.ok (suffixJson d p nodes (front ++ rest.flatten))) := by
  induction rest generalizing front with
  | nil =>
    have nonempty : deviceFixedAttrs d ≠ [] := by simp [deviceFixedAttrs]
    cases endpoint : p.endpoint <;> simp [paginationMessages,paginationTailMessages,coalesce,socketFirstPeer,
      suffixJson,peerFixedAttrs,endpoint,nonempty,List.forIn_cons,List.forIn_nil,
      ipv4Jsons,ipv4NodeJson]
  | cons ids rest ih =>
    change coalesce (.data 2 (deviceFixedAttrs d) (some [socketFirstPeer p nodes front]) ::
      .data 2 (deviceFixedAttrs d) (some [{suffixLast p nodes ids with split := !rest.isEmpty}]) ::
        paginationTailMessages d p nodes rest) = _
    rw [coalesce_merge_continuation_endpoint d p nodes front ids (!rest.isEmpty)
      (paginationTailMessages d p nodes rest)]
    change coalesce (paginationMessages d p nodes (front ++ ids) rest) = _
    rw [ih]
    simp only [List.flatten_cons,List.append_assoc]
end Leanux.Proofs.WG.Config
