import Leanux.Proofs.WG.Config.PeerPageTailModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- Exact greedy prefixes depend only on each peer's serialized cost. -/
theorem peerPagePrefix_costs_congr (peers values : PeerId → Peer)
    (cost : ∀ q, peerFixedSpace (values q) = peerFixedSpace (peers q))
    (room : Nat) (ids : List PeerId) :
    peerPagePrefix values room ids = peerPagePrefix peers room ids := by
  induction ids generalizing room with
  | nil => rfl
  | cons id ids ih =>
    simp only [peerPagePrefix,cost id]
    split
    · rw [ih]
    · rfl

/-- Resumed canonical pages retain their exact occurrence boundaries when
serialized costs agree. -/
theorem peerTailPages_costs_congr (peers values : PeerId → Peer)
    (cost : ∀ q, peerFixedSpace (values q) = peerFixedSpace (peers q))
    (room : Nat) (ids : List PeerId) :
    peerTailPages values room ids = peerTailPages peers room ids := by
  cases idsEq : ids with
  | nil => simp only [peerTailPages]
  | cons id ids =>
    rw [peerTailPages,peerTailPages,cost id,peerPagePrefix_costs_congr peers values cost]
    exact congrArg (List.cons (id :: (peerPagePrefix peers (room-peerFixedSpace (peers id)) ids).1))
      (peerTailPages_costs_congr peers values cost room
        (peerPagePrefix peers (room-peerFixedSpace (peers id)) ids).2)
termination_by ids.length
decreasing_by
  have h := congrArg List.length (peerPagePrefix_spec peers (room-peerFixedSpace (peers id)) ids).1
  simp only [List.length_append] at h
  simp only [List.length_cons]
  omega

/-- Prefix size, peer costs and lifetime fields transport the exact page plan,
DATA/DONE count and the computed nonfinal-cursor data. -/
theorem peerPage_inputs_congr (d current : Device) (peers values : PeerId → Peer)
    (space : devicePrefixSpace current = devicePrefixSpace d)
    (cost : ∀ q, peerFixedSpace (values q) = peerFixedSpace (peers q))
    (dead : ∀ q, (values q).isDead = (peers q).isDead)
    (refs : ∀ q, (values q).refcount = (peers q).refcount)
    (ids : List PeerId) :
    peerPages values current ids = peerPages peers d ids ∧
      peerPageReceiveCount values current ids = peerPageReceiveCount peers d ids ∧
      (PeerPageCursorData values (peerPages values current ids) ↔
        PeerPageCursorData peers (peerPages peers d ids)) := by
  have plan : peerPages values current ids = peerPages peers d ids := by
    simp only [peerPages,space,peerPagePrefix_costs_congr peers values cost,
      peerTailPages_costs_congr peers values cost]
  have sum (pids : List PeerId) : multiPeerSpace values pids = multiPeerSpace peers pids := by
    unfold multiPeerSpace
    congr 1
    apply List.map_congr_left
    intro q _
    exact cost q
  have lifetime (pages : List (List PeerId)) :
      PeerPageCursorData values pages ↔ PeerPageCursorData peers pages := by
    induction pages with
    | nil => rfl
    | cons page rest ih =>
      cases rest with
      | nil => rfl
      | cons next rest => simp only [PeerPageCursorData,dead,refs,ih]
  refine ⟨plan,?_,?_⟩
  · simp only [peerPageReceiveCount,peerPageFinalRoom,plan,space,sum]
    rfl
  · rw [plan]
    exact lifetime _

end Leanux.Proofs.WG.Config
