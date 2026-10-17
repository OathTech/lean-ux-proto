import Leanux.Proofs.WG.Config.TwoPageCoalesceSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- Two complete-peer DATA pages collapse into their ordered concatenation.
The arbitrary remaining messages and all their possible errors are retained. -/
theorem coalesce_complete_pages_merge (d : Device) (peers : PeerId → Peer)
    (front next : List PeerId) (tail : List NlMessage) :
    coalesce (.data 2 (deviceFixedAttrs d) (some (multiPeerParts peers front)) ::
      .data 2 [] (some (multiPeerParts peers next)) :: tail) =
    coalesce (.data 2 (deviceFixedAttrs d) (some (multiPeerParts peers (front ++ next))) :: tail) := by
  have nonempty : deviceFixedAttrs d ≠ [] := by simp [deviceFixedAttrs]
  have first := coalescePeers_complete_front #[] (multiPeerParts peers front) (Or.inl rfl)
  have second := coalescePeers_complete_front
    ((multiPeerParts peers front).map peerDumpWithIps).toArray
    (multiPeerParts peers next) (complete_parts_last peers front)
  have together := coalescePeers_complete_front #[] (multiPeerParts peers (front ++ next)) (Or.inl rfl)
  simp [coalesce, nonempty]
  conv in (forIn (multiPeerParts peers front) _ _) =>
    arg 3
    tactic =>
      exact show _ = coalescePeerStep from by
        funext p state
        simp [coalescePeerStep,peerDumpWithIps]
        congr 3
  rw [first]
  simp only [Array.empty_append, pure_bind]
  conv in (forIn (multiPeerParts peers next) _ _) =>
    arg 3
    tactic =>
      exact show _ = coalescePeerStep from by
        funext p state
        simp [coalescePeerStep,peerDumpWithIps]
        congr 3
  conv in (forIn (multiPeerParts peers (front ++ next)) _ _) =>
    arg 3
    tactic =>
      exact show _ = coalescePeerStep from by
        funext p state
        simp [coalescePeerStep,peerDumpWithIps]
        congr 3
  rw [second,together]
  simp [multiPeerParts,List.map_append]

end Leanux.Proofs.WG.Config
