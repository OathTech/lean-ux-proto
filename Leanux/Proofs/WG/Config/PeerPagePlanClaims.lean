import Leanux.Proofs.WG.Config.PeerPagePlanModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- Every resumed page fits and progresses; flattening retains every occurrence
in order, and there cannot be more resumed pages than peer occurrences. -/
theorem peerTailPages_spec (peers : PeerId → Peer) (room : Nat)
    (enough : 168 ≤ room) (ids : List PeerId) :
    (peerTailPages peers room ids).flatten = ids ∧
      (∀ page ∈ peerTailPages peers room ids, page ≠ [] ∧ multiPeerSpace peers page ≤ room) ∧
      (peerTailPages peers room ids).length ≤ ids.length := by
  cases ids with
  | nil => simp [peerTailPages]
  | cons id ids =>
    let result := peerPagePrefix peers (room - peerFixedSpace (peers id)) ids
    have facts := peerPagePrefix_spec peers (room - peerFixedSpace (peers id)) ids
    have rest := peerTailPages_spec peers room enough result.2
    have bound := peerFixedSpace_bound (peers id)
    rw [peerTailPages]
    refine ⟨?_,?_,?_⟩
    · change (id :: result.1) ++ (peerTailPages peers room result.2).flatten = id :: ids
      rw [rest.1,List.cons_append]
      exact congrArg (List.cons id) facts.1
    · intro page member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · refine ⟨by simp,?_⟩
        simp only [multiPeerSpace,List.map_cons,List.sum_cons]
        change peerFixedSpace (peers id) + multiPeerSpace peers result.1 ≤ room
        have h : multiPeerSpace peers result.1 ≤ room - peerFixedSpace (peers id) := facts.2.1
        omega
      · exact rest.2.1 page member
    · have decomp := congrArg List.length facts.1
      simp only [List.length_append] at decomp
      change (peerTailPages peers room result.2).length + 1 ≤ ids.length + 1
      have h := rest.2.2
      change result.1.length + result.2.length = ids.length at decomp
      omega
termination_by ids.length
decreasing_by
  have decomp := congrArg List.length (peerPagePrefix_spec peers
    (room - peerFixedSpace (peers id)) ids).1
  simp only [List.length_append] at decomp
  dsimp [result]
  omega

/-- The exact canonical plan retains order and duplicates. A nonempty input's
first head must fit; this excludes the real no-progress first-page case. -/
theorem peerPages_spec (peers : PeerId → Peer) (d : Device) (ids : List PeerId)
    (firstFits : ∀ id rest, ids = id :: rest →
      peerFixedSpace (peers id) ≤ NLMSG_GOODSIZE - devicePrefixSpace d) :
    (peerPages peers d ids).flatten = ids ∧
      (peerPages peers d ids) ≠ [] ∧
      multiPeerSpace peers (peerPagePrefix peers (NLMSG_GOODSIZE - devicePrefixSpace d) ids).1 ≤
        NLMSG_GOODSIZE - devicePrefixSpace d ∧
      (∀ page ∈ (peerPages peers d ids).tail,
        page ≠ [] ∧ multiPeerSpace peers page ≤ NLMSG_GOODSIZE - 24) ∧
      (peerPages peers d ids).length ≤ max 1 ids.length := by
  let first := peerPagePrefix peers (NLMSG_GOODSIZE - devicePrefixSpace d) ids
  have split := peerPagePrefix_spec peers (NLMSG_GOODSIZE - devicePrefixSpace d) ids
  have tail := peerTailPages_spec peers (NLMSG_GOODSIZE - 24) (by decide) first.2
  refine ⟨?_,by simp [peerPages],split.2.1,tail.2.1,?_⟩
  · change first.1 ++ (peerTailPages peers (NLMSG_GOODSIZE - 24) first.2).flatten = ids
    rw [tail.1]
    exact split.1
  · change (peerTailPages peers (NLMSG_GOODSIZE - 24) first.2).length + 1 ≤ max 1 ids.length
    cases ids with
    | nil => simp [first,peerPagePrefix,peerTailPages]
    | cons id ids =>
      have nonempty := (peerPagePrefix_progress peers (NLMSG_GOODSIZE - devicePrefixSpace d)
        id ids (firstFits id ids rfl)).2
      have bound := tail.2.2
      change first.2.length < (id :: ids).length at nonempty
      omega

/-- Convenient boundary form for the native front-plus-last cursor source. -/
theorem peerPageBoundaryFresh_cons (before front : List PeerId) (cursor : PeerId)
    (next : List PeerId) (rest : List (List PeerId)) :
    peerPageBoundaryFresh before ((front ++ [cursor]) :: next :: rest) ↔
      cursor ∉ before ++ front ∧
      peerPageBoundaryFresh (before ++ (front ++ [cursor])) (next :: rest) := by
  simp [peerPageBoundaryFresh]

/-- A finite sufficient bound for the unchanged original receive budget. This
is a pure plan count; native execution correspondence is a separate obligation. -/
theorem peerPageReceiveCount_bound (peers : PeerId → Peer) (d : Device) (ids : List PeerId)
    (firstFits : ∀ id rest, ids = id :: rest →
      peerFixedSpace (peers id) ≤ NLMSG_GOODSIZE - devicePrefixSpace d) :
    1 ≤ peerPageReceiveCount peers d ids ∧
      peerPageReceiveCount peers d ids ≤ max 1 ids.length + 1 := by
  have facts := peerPages_spec peers d ids firstFits
  have nonempty : 0 < (peerPages peers d ids).length := by
    simp [peerPages]
  have bound := facts.2.2.2.2
  unfold peerPageReceiveCount
  split <;> omega

end Leanux.Proofs.WG.Config
