import Leanux.Proofs.WG.Config.TwoPageCoalesceSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- The actual coalescer appends two pages of complete peer occurrences in
order, with device attributes only on the first page and a successful DONE.
This does not assert that a getter produced the supplied pages. -/
theorem coalesce_two_complete_pages (d : Device) (peers : PeerId → Peer)
    (front tail : List PeerId) :
    coalesce [.data 2 (deviceFixedAttrs d) (some (multiPeerParts peers front)),
      .data 2 [] (some (multiPeerParts peers tail)), .done 2 0] =
      pure (.ok (Json.mkObj (deviceFixedAttrs d ++ [("peers",Json.arr
        (((multiPeerParts peers (front ++ tail)).map peerDumpWithIps).toArray.map
          fun p => Json.mkObj p.attrs))]))) := by
  have nonempty : deviceFixedAttrs d ≠ [] := by simp [deviceFixedAttrs]
  have first := coalescePeers_complete_front #[] (multiPeerParts peers front) (Or.inl rfl)
  have second := coalescePeers_complete_front
    ((multiPeerParts peers front).map peerDumpWithIps).toArray
    (multiPeerParts peers tail) (complete_parts_last peers front)
  have factor : coalesce [.data 2 (deviceFixedAttrs d) (some (multiPeerParts peers front)),
      .data 2 [] (some (multiPeerParts peers tail)), .done 2 0] =
      (do let first ← forIn (multiPeerParts peers front) (#[],true) coalescePeerStep
          let second ← forIn (multiPeerParts peers tail) (first.1,true) coalescePeerStep
          pure (.ok (Json.mkObj (deviceFixedAttrs d ++ [("peers",Json.arr
            (second.1.map fun p => Json.mkObj p.attrs))])))) := by
    unfold coalescePeerStep
    simp [coalesce,nonempty,peerDumpWithIps]
    congr 3
  rw [factor,first]
  simp only [Array.empty_append, pure_bind]
  rw [second]
  simp [multiPeerParts,List.map_append]
end Leanux.Proofs.WG.Config
