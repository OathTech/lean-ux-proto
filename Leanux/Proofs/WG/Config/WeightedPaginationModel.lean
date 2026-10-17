import Leanux.Proofs.WG.Config.MixedDumpModel
import Leanux.Proofs.WG.Config.SocketReadbackModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- Greedily take the exact fitting prefix; a failing next node is retained. -/
def weightedPrefix (nodes : NodeId → AipNode) : Nat → List NodeId → List NodeId × List NodeId
  | _, [] => ([], [])
  | room, id :: ids =>
    if dumpNodeSpace (nodes id) ≤ room then
      let result := weightedPrefix nodes (room - dumpNodeSpace (nodes id)) ids
      (id :: result.1, result.2)
    else ([], id :: ids)

/-- The plan decomposes the actual list, fits, and stops at its first failing
node. Widths, IDs, and their repetition are unrestricted. -/
theorem weightedPrefix_spec (nodes : NodeId → AipNode) (room : Nat) (ids : List NodeId) :
    let result := weightedPrefix nodes room ids
    result.1 ++ result.2 = ids ∧ dumpNodesSpace nodes result.1 ≤ room ∧
      ∀ next tail, result.2 = next :: tail →
        room < dumpNodesSpace nodes result.1 + dumpNodeSpace (nodes next) := by
  induction ids generalizing room with
  | nil => simp [weightedPrefix, dumpNodesSpace]
  | cons id ids ih =>
    by_cases fits : dumpNodeSpace (nodes id) ≤ room
    · simp only [weightedPrefix, ite_eq_left fits]
      obtain ⟨decomp, space, short⟩ := ih (room - dumpNodeSpace (nodes id))
      refine ⟨by simpa only [List.cons_append] using congrArg (List.cons id) decomp, ?_, ?_⟩
      · simp only [dumpNodesSpace, List.map_cons, List.sum_cons]
        change dumpNodeSpace (nodes id) + dumpNodesSpace nodes _ ≤ room
        omega
      · intro next tail remainder
        have h := short next tail remainder
        simp only [dumpNodesSpace, List.map_cons, List.sum_cons]
        change room < dumpNodeSpace (nodes id) + dumpNodesSpace nodes _ + dumpNodeSpace (nodes next)
        omega
    · simp only [weightedPrefix, ite_eq_right fits]
      refine ⟨rfl, by simp [dumpNodesSpace], ?_⟩
      intro next tail equality
      cases equality
      simp only [dumpNodesSpace, List.map_nil, List.sum_nil, Nat.zero_add]
      omega

/-- An actually fitting first node is emitted, so the remainder is strictly
shorter. A first-page caller need not assume this condition. -/
theorem weightedPrefix_progress (nodes : NodeId → AipNode) (room : Nat)
    (id : NodeId) (ids : List NodeId) (fits : dumpNodeSpace (nodes id) ≤ room) :
    (weightedPrefix nodes room (id :: ids)).1 ≠ [] ∧
      (weightedPrefix nodes room (id :: ids)).2.length < (id :: ids).length := by
  have decomp := congrArg List.length (weightedPrefix_spec nodes
    (room - dumpNodeSpace (nodes id)) ids).1
  simp only [List.length_append] at decomp
  simp only [weightedPrefix, ite_eq_left fits, List.length_cons, ne_eq, List.cons_ne_nil, not_false_eq_true, true_and]
  omega

theorem dumpNodeSpace_bounds (n : AipNode) : 28 ≤ dumpNodeSpace n ∧ dumpNodeSpace n ≤ 40 := by
  unfold dumpNodeSpace
  split <;> omega

/-- Resumed pages consume a first node, then use the same greedy rule for
the remaining room. The later source domain guarantees the first node fits. -/
def weightedTailPages (nodes : NodeId → AipNode) (room : Nat) : List NodeId → List (List NodeId)
  | [] => []
  | id :: ids =>
    let result := weightedPrefix nodes (room - dumpNodeSpace (nodes id)) ids
    (id :: result.1) :: weightedTailPages nodes room result.2
termination_by ids => ids.length
decreasing_by
  have decomp := congrArg List.length (weightedPrefix_spec nodes
    (room - dumpNodeSpace (nodes id)) ids).1
  simp only [List.length_append] at decomp
  simp_wf
  omega

/-- Every resumed page is nonempty and fits, and concatenation retains every
original occurrence in order. The cost bound ensures progress for all widths. -/
theorem weightedTailPages_spec (nodes : NodeId → AipNode) (room : Nat)
    (enough : 40 ≤ room) (ids : List NodeId) :
    (weightedTailPages nodes room ids).flatten = ids ∧
      ∀ page ∈ weightedTailPages nodes room ids, page ≠ [] ∧ dumpNodesSpace nodes page ≤ room := by
  cases ids with
  | nil => simp [weightedTailPages]
  | cons id ids =>
    let result := weightedPrefix nodes (room - dumpNodeSpace (nodes id)) ids
    have facts := weightedPrefix_spec nodes (room - dumpNodeSpace (nodes id)) ids
    have rest := weightedTailPages_spec nodes room enough result.2
    have bound := (dumpNodeSpace_bounds (nodes id)).2
    rw [weightedTailPages]
    refine ⟨?_, ?_⟩
    · change (id :: result.1) ++ (weightedTailPages nodes room result.2).flatten = id :: ids
      rw [rest.1, List.cons_append]
      exact congrArg (List.cons id) facts.1
    · intro page member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · refine ⟨by simp, ?_⟩
        simp only [dumpNodesSpace, List.map_cons, List.sum_cons]
        change dumpNodeSpace (nodes id) + dumpNodesSpace nodes result.1 ≤ room
        have h : dumpNodesSpace nodes result.1 ≤ room - dumpNodeSpace (nodes id) := facts.2.1
        omega
      · exact rest.2 page member
termination_by ids.length
decreasing_by
  have decomp := congrArg List.length (weightedPrefix_spec nodes
    (room - dumpNodeSpace (nodes id)) ids).1
  simp only [List.length_append] at decomp
  dsimp [result]
  omega

/-- A possibly empty first prefix followed only by progressing resumed pages.
An empty input still describes one DATA page; its raw attributes are handled
separately by the original no-allowed-IPs branch. -/
def weightedPages (nodes : NodeId → AipNode) (firstRoom resumeRoom : Nat) (ids : List NodeId) : List (List NodeId) :=
  let result := weightedPrefix nodes firstRoom ids
  result.1 :: weightedTailPages nodes resumeRoom result.2

theorem weightedPages_spec (nodes : NodeId → AipNode) (firstRoom resumeRoom : Nat)
    (enough : 40 ≤ resumeRoom) (ids : List NodeId) :
    (weightedPages nodes firstRoom resumeRoom ids).flatten = ids ∧
      dumpNodesSpace nodes (weightedPrefix nodes firstRoom ids).1 ≤ firstRoom ∧
      ∀ page ∈ (weightedPages nodes firstRoom resumeRoom ids).tail,
        page ≠ [] ∧ dumpNodesSpace nodes page ≤ resumeRoom := by
  have first := weightedPrefix_spec nodes firstRoom ids
  have rest := weightedTailPages_spec nodes resumeRoom enough (weightedPrefix nodes firstRoom ids).2
  exact ⟨by simpa only [weightedPages, List.flatten_cons, rest.1] using first.1,
    first.2.1, rest.2⟩

/-- A resumed boundary must be fresh against ALL earlier emitted IDs. Empty
resumed pages are disallowed; repeated IDs elsewhere are not excluded. -/
def weightedBoundaryFresh (before : List NodeId) : List (List NodeId) → Prop
  | [] => True
  | [] :: _ => False
  | (start :: rest) :: pages => start ∉ before ∧
      weightedBoundaryFresh (before ++ start :: rest) pages

/-- Exact resumed callback data, using the original 40-byte peer prefix and
four-byte allowed-IP nest. The source theorem derives this value from the
actual callback, including its cursor lookup and complete/split decision. -/
def mixedResumeCall (d : Device) (p : Peer) (nodes : NodeId → AipNode)
    (start : NodeId) (rest : List NodeId) : DumpCall :=
  let result := weightedPrefix nodes (NLMSG_GOODSIZE - devicePrefixSpace d - 44) (start :: rest)
  let attrs := [("public_key", toJson (hexKey p.remoteStatic)),
    ("allowed_ips", Json.arr (dumpNodeJsons nodes result.1))]
  let ctx : DumpCtx := match result.2 with
    | [] => {hasWg := true}
    | next :: _ => {hasWg := true, nextAllowedip := some next, allowedipsSeq := d.peerAllowedips.seq}
  socketCallbackResult d ctx
    (NLMSG_GOODSIZE - (devicePrefixSpace d + 44 + dumpNodesSpace nodes result.1))
    {publicKey := hexKey p.remoteStatic, attrs, split := !result.2.isEmpty} (!result.2.isEmpty)

end Leanux.Proofs.WG.Config
