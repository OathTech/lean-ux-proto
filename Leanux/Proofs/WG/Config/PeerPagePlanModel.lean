import Leanux.Proofs.WG.Config.MultiPeerDumpModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- Exact fixed-peer cost prefix. An unfit first peer is retained, never forced. -/
def peerPagePrefix (peers : PeerId → Peer) : Nat → List PeerId → List PeerId × List PeerId
  | _, [] => ([], [])
  | room, id :: ids =>
    if peerFixedSpace (peers id) ≤ room then
      let result := peerPagePrefix peers (room - peerFixedSpace (peers id)) ids
      (id :: result.1, result.2)
    else ([], id :: ids)

/-- Exact ordered split, fitting cost, and first excluded peer's maximality. -/
theorem peerPagePrefix_spec (peers : PeerId → Peer) (room : Nat) (ids : List PeerId) :
    let result := peerPagePrefix peers room ids
    result.1 ++ result.2 = ids ∧ multiPeerSpace peers result.1 ≤ room ∧
      ∀ next tail, result.2 = next :: tail →
        room < multiPeerSpace peers result.1 + peerFixedSpace (peers next) := by
  induction ids generalizing room with
  | nil => simp [peerPagePrefix,multiPeerSpace]
  | cons id ids ih =>
    by_cases fits : peerFixedSpace (peers id) ≤ room
    · simp only [peerPagePrefix,ite_eq_left fits]
      obtain ⟨decomp,space,short⟩ := ih (room - peerFixedSpace (peers id))
      refine ⟨by simpa only [List.cons_append] using congrArg (List.cons id) decomp,?_,?_⟩
      · simp only [multiPeerSpace,List.map_cons,List.sum_cons]
        change peerFixedSpace (peers id) + multiPeerSpace peers _ ≤ room
        omega
      · intro next tail remainder
        have h := short next tail remainder
        simp only [multiPeerSpace,List.map_cons,List.sum_cons]
        change room < peerFixedSpace (peers id) + multiPeerSpace peers _ + peerFixedSpace (peers next)
        omega
    · simp only [peerPagePrefix,ite_eq_right fits]
      refine ⟨rfl,by simp [multiPeerSpace],?_⟩
      intro next tail equality
      cases equality
      simp only [multiPeerSpace,List.map_nil,List.sum_nil,Nat.zero_add]
      omega

/-- A fitting first peer makes genuine progress, without a distinct-ID premise. -/
theorem peerPagePrefix_progress (peers : PeerId → Peer) (room : Nat)
    (id : PeerId) (ids : List PeerId) (fits : peerFixedSpace (peers id) ≤ room) :
    (peerPagePrefix peers room (id :: ids)).1 ≠ [] ∧
      (peerPagePrefix peers room (id :: ids)).2.length < (id :: ids).length := by
  have decomp := congrArg List.length (peerPagePrefix_spec peers
    (room - peerFixedSpace (peers id)) ids).1
  simp only [List.length_append] at decomp
  simp only [peerPagePrefix,ite_eq_left fits,List.length_cons,ne_eq,List.cons_ne_nil,not_false_eq_true,true_and]
  omega

/-- Nonempty resumed pages use one fitting head and greedily fill their rest.
The 168-byte bound below establishes that head's fit in the real resumed room. -/
def peerTailPages (peers : PeerId → Peer) (room : Nat) : List PeerId → List (List PeerId)
  | [] => []
  | id :: ids =>
    let result := peerPagePrefix peers (room - peerFixedSpace (peers id)) ids
    (id :: result.1) :: peerTailPages peers room result.2
termination_by ids => ids.length
decreasing_by
  have decomp := congrArg List.length (peerPagePrefix_spec peers
    (room - peerFixedSpace (peers id)) ids).1
  simp only [List.length_append] at decomp
  simp_wf
  omega

/-- First DATA uses the real Device prefix; every resume uses the 24-byte
message header and peer nest. Empty input still produces one DATA page. -/
def peerPages (peers : PeerId → Peer) (d : Device) (ids : List PeerId) : List (List PeerId) :=
  let first := peerPagePrefix peers (NLMSG_GOODSIZE - devicePrefixSpace d) ids
  first.1 :: peerTailPages peers (NLMSG_GOODSIZE - 24) first.2

/-- Every nonfinal cursor is the LAST emitted peer. Its first occurrence must
be that position, excluding every earlier occurrence, even within its page.
Final-page peers need no cursor freshness or ownership condition. -/
def peerPageBoundaryFresh (before : List PeerId) : List (List PeerId) → Prop
  | [] => True
  | [_] => True
  | page :: next :: rest =>
    page ≠ [] ∧ (∀ cursor, page.getLast? = some cursor → cursor ∉ before ++ page.dropLast) ∧
      peerPageBoundaryFresh (before ++ page) (next :: rest)

/-- Room in the final DATA before the actual DONE-size test. The mirror's
empty-peer cancellation retains the already-reserved nest space; see the
checked DumpCancellation finding. -/
def peerPageFinalRoom (peers : PeerId → Peer) (d : Device) (ids : List PeerId) : Nat :=
  let pages := peerPages peers d ids
  let room := if pages.tail.isEmpty then NLMSG_GOODSIZE - devicePrefixSpace d else NLMSG_GOODSIZE - 24
  room - multiPeerSpace peers (pages.getLastD [])

/-- One receive per DATA page plus the actual final DONE spill bit. -/
def peerPageReceiveCount (peers : PeerId → Peer) (d : Device) (ids : List PeerId) : Nat :=
  (peerPages peers d ids).length +
    if peerPageFinalRoom peers d ids < nlmsgTotal 4 then 1 else 0


end Leanux.Proofs.WG.Config
