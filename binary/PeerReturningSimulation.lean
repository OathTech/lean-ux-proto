import PeerLiveSimulation

namespace Binary.LookupRelation
open Leanux Leanux.WG LookupObservation PeerCountPhase

/-- Dead/NULL helper interior: its actual history has no pending increment,
    and all WG read fields follow the executed byte frame. -/
theorem returning_interior (c : Config) (world : World) (s : MachineState)
    (history tail interior : List MachineState) (current : MachineState)
    (seen delta : List Point) (sourceHistory : List MirrorHistory.Point)
    (related : R c history seen s world)
    (observed : observe c.rxSection history = .ok seen)
    (frontObs : observe c.rxSection (history ++ interior) = .ok (seen ++ delta))
    (matched : MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection history) seen sourceHistory)
    (aligned : ExecutedCorrespondence.CutsAligned (R c) c.rxSection history sourceHistory)
    (latest : sourceHistory.getLast?.map (·.world) = some world)
    (tags : LookupHistory.DecisionPoints delta)
    (helperTags : ∀ point ∈ delta, HelperTag point.tag)
    (active : helperActive seen = true) (noReturn : lastHelperReturn seen = none)
    (phase : ReturningExtension history (history ++ tail))
    (splitHistory : (history ++ interior) ++ [current] = history ++ tail)
    (initial : scan none history = none) (writes : Address → Prop)
    (frames : ∀ q ∈ tail, q.pc ∈ Image.cutPoints → EqualOutside writes s.data.dmem q.data.dmem)
    (apart : ∀ v, project c world = some v → ∀ a, Reads c v a → ¬writes a) :
    MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection (history ++ interior))
      (seen ++ delta) (sourceHistory ++ LookupSearch.decisionWorlds world (delta.filterMap (·.step))) ∧
    ExecutedCorrespondence.CutsAligned (R c) c.rxSection (history ++ interior)
      (sourceHistory ++ LookupSearch.decisionWorlds world (delta.filterMap (·.step))) := by
  have cuts : ∀ point ∈ delta, point.machine.pc ∈ Image.cutPoints := by
    intro point member
    exact observe_helper_cuts _ _ _ frontObs point (List.mem_append.mpr (.inr member)) (helperTags point member)
  have frontFrames : ∀ q ∈ interior, q.pc ∈ Image.cutPoints → EqualOutside writes s.data.dmem q.data.dmem := by
    intro q member cut
    have tails : interior ++ [current] = tail := by
      apply List.append_cancel_left (as := history)
      simpa only [List.append_assoc] using splitHistory
    apply frames q _ cut
    rw [← tails]
    simp [member]
  have bucketApart : ∀ v, project c world = some v → ∀ a, TrustBase.LookupBucketBytes c v a → ¬writes a := by
    intro v projected a read
    apply apart v projected a
    rcases read with head | node
    · exact .inl head
    · exact .inr (.inl node)
  have ownerApart : ∀ a, TrustBase.LookupOwnerBytes c a → ¬writes a := by
    intro a read
    obtain ⟨v, projected, _⟩ := related.2.1
    exact apart v projected a (.inr (.inr (.inl read)))
  have counts : ∀ i q, (history ++ interior)[i]? = some q → history.length ≤ i →
      q.pc ∈ Image.cutPoints → ∀ events, helperActive events = true →
      ∀ v, project c world = some v → ∀ other number,
      c.focus.peer = some other → v.count = some number →
      At (countPhase ((history ++ interior).take (i+1)) events) q.data.dmem
        (c.peers other + .ofNat 64 Layouts.peer_refcount) number := by
    intro i q present later cut events activeNow v projected other number focusOther count
    have before := (List.getElem?_eq_some_iff.mp present).1
    have presentFull : (history ++ tail)[i]? = some q := by
      rw [← splitHistory, List.getElem?_append_left before]
      exact present
    have loaded := related.initial_count c history seen s world initial v projected other focusOther number count
    have phaseNone : scan none ((history ++ tail).take (i+1)) = none := by
      rw [phase.at_prefix none (i+1) (by omega), initial]
      split <;> rfl
    have asCount : countPhase ((history ++ tail).take (i+1)) events = none := by
      simp only [countPhase, phaseNone, ite_self]
    have asFront : countPhase ((history ++ interior).take (i+1)) events = none := by
      simpa only [← splitHistory, List.take_append_of_le_length (by omega : i+1 ≤ (history ++ interior).length)] using asCount
    rw [asFront]
    have member : q ∈ interior := by
      exact List.mem_of_getElem? (by simpa only [List.getElem?_append_right later] using present)
    exact PeerCountPhase.At.frame (frontFrames q member cut)
      (fun j hj => apart v projected _ (.inr (.inr (.inr ⟨other, focusOther, j, hj, rfl⟩)))) loaded

  have points := helper_decision_points c world s history interior seen delta related observed frontObs tags cuts
    noReturn writes frontFrames bucketApart ownerApart (by
      intro i point before after decomposition later present v projected other number focusOther count
      have member : point ∈ delta := by rw [decomposition]; simp
      have partTags : LookupHistory.DecisionPoints (before ++ [point]) := by
        intro q qMember
        apply tags q
        rw [decomposition]
        rcases List.mem_append.mp qMember with first | last
        · exact List.mem_append.mpr (.inl first)
        · have same := List.mem_singleton.mp last
          subst q
          simp
      exact counts i point.machine present later (cuts point member) _
        (by rw [helperActive_append_decisions _ _ partTags, active]) v projected other number focusOther count)
  have fullMatched := (ExecutedCorrespondence.matched_append_history matched interior).append
    (by simpa only [List.nil_append] using points)
  exact ⟨fullMatched, helper_decision_cuts c world s history interior seen delta sourceHistory related observed frontObs
    matched fullMatched aligned latest tags active noReturn writes frontFrames bucketApart ownerApart counts⟩

#print axioms returning_interior
end Binary.LookupRelation
