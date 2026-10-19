import LookupOwnerRelation
import LookupOwnerSource

namespace Binary.LookupRelation
open Leanux Leanux.WG LookupObservation

/-- A retained actual helper return ends its count phase. -/
theorem helper_inactive_of_return (seen : List Point) (snapshot : MachineState)
    (returned : lastHelperReturn seen = some snapshot) : helperActive seen = false := by
  cases last : seen.getLast? with
  | none => simp [lastHelperReturn, last] at returned
  | some point =>
    obtain ⟨front, eq⟩ := List.getLast?_eq_some_iff.mp last
    cases tag : point.tag with
    | decision d => simp [lastHelperReturn, last, tag] at returned
    | call name => simp [lastHelperReturn, last, tag] at returned
    | returned name =>
      by_cases nameEq : name = "wg_peer_get_maybe_zero"
      · rw [eq]
        simp [helperActive, helperTag, tag, nameEq]
      · simp [lastHelperReturn, last, tag, nameEq] at returned

private theorem result_frame (s : MachineData) (af : Bool) (q : MachineState)
    (member : q ∈ LookupHistory.resultStates s af) :
    EqualOutside (InRange s.regs.rbx.toBitVec 8) s.dmem q.data.dmem := by
  rw [LookupHistory.resultStates_memory s af q member]
  exact OwnerWord.stored_frame s

/-- Every pre-decision result cut still represents the helper-return World.
    Its owner word is pending, sourced from that actual return snapshot. -/
theorem R.result_pending (c : Config) (world : World) (s : MachineData)
    (raw raw' : List MachineState) (seen : List Point)
    (related : R c raw seen ⟨s, Image.Lookup.entry+0xba⟩ world)
    (returned : lastHelperReturn seen = some ⟨s, Image.Lookup.entry+0xba⟩)
    (owner : IndexOwner) (focused : c.focus.owner = some owner)
    (location : s.regs.rbx.toBitVec = ownerAddress c owner)
    (bucketApart : ∀ v, project c world = some v → ∀ a, TrustBase.LookupBucketBytes c v a →
      ¬InRange (ownerAddress c owner) 8 a)
    (countApart : ∀ a, TrustBase.LookupCountBytes c a → ¬InRange (ownerAddress c owner) 8 a)
    (af : Bool) (q : MachineState) (member : q ∈ LookupHistory.resultStates s af)
    (pending : OwnerWord.PendingPC q.pc) (last : raw'.getLast? = some q) :
    R c raw' seen q world := by
  obtain ⟨_, ⟨v, projected, physical⟩, steps⟩ := related
  have ownerAt := physical.2.2.1
  simp only [focused] at ownerAt
  obtain ⟨old, value, field⟩ := ownerAt
  have ordinary : ownerPending seen ⟨s, Image.Lookup.entry+0xba⟩ = none := by
    simp only [ownerPending]
    rw [if_neg (by decide)]
  simp only [OwnerFieldAt, ordinary] at field
  have ownerAt := owner_pending_result c seen s owner old returned location field af q member pending
  have framed := physical.frame_owner c raw raw' seen seen _ q v owner focused old
    (helper_inactive_of_return seen _ returned) (helper_inactive_of_return seen _ returned)
    _ (result_frame s af q member)
    (by simpa only [location] using bucketApart v projected)
    (by simpa only [location] using countApart) ownerAt
  have same : {v with ownerWord := some old} = v := by cases v; simp_all
  rw [same] at framed
  exact ⟨last, ⟨v, projected, framed⟩, steps⟩

/-- The decision successor commits the actual store into the landed source
    setter, including the dead-peer NULL store-back. -/
theorem R.result_committed (c : Config) (world setWorld : World) (s : MachineData)
    (raw raw' : List MachineState) (seen : List Point)
    (related : R c raw seen ⟨s, Image.Lookup.entry+0xba⟩ world)
    (returned : lastHelperReturn seen = some ⟨s, Image.Lookup.entry+0xba⟩)
    (owner : IndexOwner) (focused : c.focus.owner = some owner)
    (word : Option PeerId) (result : s.regs.rax.toBitVec = OwnerWord.pointer c.peers word)
    (location : s.regs.rbx.toBitVec = ownerAddress c owner)
    (setRun : (Source.setPeerWord owner word).run world = .ok ((), setWorld))
    (bucketApart : ∀ v, project c world = some v → ∀ a, TrustBase.LookupBucketBytes c v a →
      ¬InRange (ownerAddress c owner) 8 a)
    (countApart : ∀ a, TrustBase.LookupCountBytes c a → ¬InRange (ownerAddress c owner) 8 a)
    (af : Bool) (last : raw'.getLast? = some (LookupHistory.resultExit s af)) :
    R c raw' (seen ++ [decision c.rxSection .idxPeerAlive (decide (s.regs.rax ≠ 0)) (LookupHistory.resultExit s af)])
      (LookupHistory.resultExit s af)
      (LookupMirror.record setWorld .idxPeerAlive (decide (s.regs.rax ≠ 0))) := by
  obtain ⟨_, ⟨v, projected, physical⟩, steps⟩ := related
  have ownerAt := physical.2.2.1
  simp only [focused] at ownerAt
  obtain ⟨old, value, _⟩ := ownerAt
  obtain ⟨setWorld', setRun', projectSet, sameSteps, sameRx⟩ := owner_set_project c world v owner old word projected focused value
  have sameWorld : setWorld' = setWorld := (Prod.mk.inj (Except.ok.inj (setRun'.symm.trans setRun))).2
  subst setWorld'
  let delta := [decision c.rxSection .idxPeerAlive (decide (s.regs.rax ≠ 0)) (LookupHistory.resultExit s af)]
  have inactive := helper_inactive_of_return seen _ returned
  have inactive' : helperActive (seen ++ delta) = false := by
    rw [helperActive_decision]
    exact inactive
  have member : LookupHistory.resultExit s af ∈ LookupHistory.resultStates s af := by simp [LookupHistory.resultStates]
  have framed := physical.frame_owner c raw raw' seen (seen ++ delta) _ (LookupHistory.resultExit s af) v owner focused word
    inactive inactive' _ (result_frame s af _ member)
    (by simpa only [location] using bucketApart v projected)
    (by simpa only [location] using countApart)
    (owner_committed_result c _ s owner word location result af)
  refine ⟨last, ⟨{v with ownerWord := some word}, ?_, framed⟩, ?_⟩
  · exact projectSet
  · have stepSet : StepsAt c seen setWorld := ⟨by rw [sameSteps]; exact steps.1, sameRx.trans steps.2⟩
    have advanced := stepSet.advance c seen delta setWorld
    simpa only [delta, List.filterMap_cons, decision, List.filterMap_nil, LookupSearch.advance,
      LookupSearch.recordStep, LookupMirror.record, stepSet.2] using advanced

#print axioms helper_inactive_of_return
#print axioms R.result_pending
#print axioms R.result_committed
end Binary.LookupRelation
