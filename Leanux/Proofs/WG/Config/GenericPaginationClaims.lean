import Leanux.Proofs.WG.Config.GenericPaginationModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- Merge adjacent actual DATA continuations before the unchanged remainder,
including its errors. Entries are arbitrary JSON and endpoints unrestricted. -/
theorem coalesce_merge_json_continuation (d : Device) (p : Peer)
    (front ips : List Json) (more : Bool) (tail : List NlMessage) :
    coalesce (.data 2 (deviceFixedAttrs d) (some [jsonFirstPeer p front]) ::
      .data 2 (deviceFixedAttrs d) (some [{jsonSuffixPeer p ips with split := more}]) :: tail) =
    coalesce (.data 2 (deviceFixedAttrs d)
      (some [{jsonFirstPeer p (front ++ ips) with split := more}]) :: tail) := by
  have nonempty : deviceFixedAttrs d ≠ [] := by simp [deviceFixedAttrs]
  cases endpoint : p.endpoint <;> simp [coalesce,jsonFirstPeer,jsonSuffixPeer,peerFixedAttrs,
    endpoint,nonempty,List.forIn_cons,List.forIn_nil,List.lookup]

/-- The actual coalescer preserves every supplied JSON entry across any finite
page sequence, including empty pages and repeated entries. This is a coalescer
contract, not a claim that a dump or receive sequence produced those pages. -/
theorem coalesce_json_pagination (d : Device) (p : Peer)
    (front : List Json) (rest : List (List Json)) :
    coalesce (jsonPaginationMessages d p front rest) =
      pure (.ok (jsonPaginationResult d p (front ++ rest.flatten))) := by
  induction rest generalizing front with
  | nil =>
    have nonempty : deviceFixedAttrs d ≠ [] := by simp [deviceFixedAttrs]
    cases endpoint : p.endpoint <;> simp [jsonPaginationMessages,jsonPaginationTailMessages,
      coalesce,jsonFirstPeer,jsonPaginationResult,peerFixedAttrs,endpoint,nonempty,
      List.forIn_cons,List.forIn_nil]
  | cons ips rest ih =>
    change coalesce (.data 2 (deviceFixedAttrs d) (some [jsonFirstPeer p front]) ::
      .data 2 (deviceFixedAttrs d) (some [{jsonSuffixPeer p ips with split := !rest.isEmpty}]) ::
        jsonPaginationTailMessages d p rest) = _
    rw [coalesce_merge_json_continuation d p front ips (!rest.isEmpty)
      (jsonPaginationTailMessages d p rest)]
    change coalesce (jsonPaginationMessages d p (front ++ ips) rest) = _
    rw [ih]
    simp only [List.flatten_cons,List.append_assoc]

end Leanux.Proofs.WG.Config
