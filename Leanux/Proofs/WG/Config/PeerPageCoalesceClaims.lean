import Leanux.Proofs.WG.Config.PeerPageCoalesceSource
import Leanux.Proofs.WG.Config.MultiPeerCoalesceClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- All complete peer pages are concatenated in occurrence order. -/
theorem coalesce_complete_pages (d : Device) (peers : PeerId → Peer)
    (first : List PeerId) (rest : List (List PeerId)) :
    coalesce (.data 2 (deviceFixedAttrs d) (some (multiPeerParts peers first)) ::
      rest.map (fun page => .data 2 [] (some (multiPeerParts peers page))) ++ [.done 2 0]) =
      pure (.ok (Json.mkObj (deviceFixedAttrs d ++ [("peers",Json.arr
        (((multiPeerParts peers (first ++ rest.flatten)).map peerDumpWithIps).toArray.map
          fun p => Json.mkObj p.attrs))]))) := by
  induction rest generalizing first with
  | nil => simpa using coalesce_single_page d (multiPeerParts peers first)
  | cons page rest ih =>
    simp only [List.map_cons, List.cons_append, List.flatten_cons]
    rw [coalesce_complete_pages_merge]
    simpa only [List.append_assoc, List.cons_append] using ih (first ++ page)

end Leanux.Proofs.WG.Config
