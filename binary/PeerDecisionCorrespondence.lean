import LookupPeerRelation
import CorrespondencePrefix

namespace Binary.LookupRelation
open Leanux TrustBase LookupHistory

/-- The actual emitting prefix of every helper decision, with the count
    equation discharged separately from its permitted write footprint.
    Return markers are composed separately because they commit the source. -/
theorem helper_decision_points (c : Config) (world : World) (s : MachineState)
    (history tail : List MachineState) (seen delta : List LookupObservation.Point)
    (related : R c history seen s world)
    (observed : LookupObservation.observe c.rxSection history = .ok seen)
    (full : LookupObservation.observe c.rxSection (history ++ tail) = .ok (seen ++ delta))
    (tags : DecisionPoints delta)
    (cuts : ∀ point ∈ delta, point.machine.pc ∈ Image.cutPoints)
    (noReturn : lastHelperReturn seen = none)
    (writes : Address → Prop)
    (frames : ∀ state ∈ tail, state.pc ∈ Image.cutPoints →
      EqualOutside writes s.data.dmem state.data.dmem)
    (bucketApart : ∀ v, project c world = some v → ∀ a, TrustBase.LookupBucketBytes c v a → ¬writes a)
    (ownerApart : ∀ a, TrustBase.LookupOwnerBytes c a → ¬writes a)
    (countAt : ∀ i point before after, delta = before ++ point :: after →
      history.length ≤ i → (history ++ tail)[i]? = some point.machine →
      ∀ v, project c world = some v → ∀ pid count,
        c.focus.peer = some pid → v.count = some count →
        PeerCountPhase.At (countPhase ((history ++ tail).take (i+1)) (seen ++ (before ++ [point])))
          point.machine.data.dmem (c.peers pid + .ofNat 64 Layouts.peer_refcount) count) :
    LookupObservation.MatchesPointsFrom
      (ExecutedCorrespondence.AtPoint (R c) c.rxSection (history ++ tail)) seen delta
      (LookupSearch.decisionWorlds world (delta.filterMap (·.step))) := by
  apply LookupSearch.match_decisions _ seen delta world tags
  intro before point after decomposition
  have pointMember : point ∈ delta := by rw [decomposition]; simp
  have pointAt : (seen ++ delta)[seen.length + before.length]? = some point := by
    rw [decomposition, ← List.append_assoc]
    simp
  obtain ⟨i, localEvents, later, stateAt, localObs, count, prefixEq, emitted⟩ :=
    LookupObservation.observe_locate_after c.rxSection history tail seen (seen ++ delta)
      observed full (seen.length + before.length) point pointAt (by omega)
  have inTail : point.machine ∈ tail := by
    have found : tail[i - history.length]? = some point.machine := by
      simpa only [List.getElem?_append_right later] using stateAt
    exact List.mem_of_getElem? found
  have partialTags : DecisionPoints (before ++ [point]) := by
    intro q present
    apply tags q
    rw [decomposition]
    rcases List.mem_append.mp present with old | last
    · exact List.mem_append.mpr (.inl old)
    · have equal : q = point := List.mem_singleton.mp last
      subst q
      simp
  have last : ((history ++ tail).take (i + 1)).getLast? = some point.machine := by
    rw [List.getLast?_take]
    simp [stateAt]
  have pointR := related.advance_count c history ((history ++ tail).take (i + 1))
    seen (before ++ [point]) s point.machine world last partialTags noReturn
    writes (frames point.machine inTail (cuts point pointMember)) bucketApart ownerApart
    (countAt i point before after decomposition later stateAt)
  have seenLength : (seen ++ before ++ [point]).length = seen.length + before.length + 1 := by simp [Nat.add_assoc]
  have exactPrefix : (seen ++ delta).take (seen.length + before.length + 1) =
      seen ++ before ++ [point] := by
    rw [decomposition, ← List.append_assoc]
    have n : seen.length + before.length + 1 = (seen ++ before).length + 1 := by simp
    rw [n, List.take_append]
    rw [List.take_of_length_le (by omega)]
    simp
  refine ⟨i, localEvents, stateAt, localObs, ?_, ?_, ?_, ?_, ?_⟩
  · intro empty
    have h := congrArg List.length empty
    simp only [seenLength, List.length_nil] at h
    omega
  · simpa only [seenLength] using count
  · rw [seenLength]
    exact exactPrefix.symm.trans prefixEq
  · rcases emitted with first | ⟨earlier, earlierObs, smaller⟩
    · exact .inl first
    · exact .inr ⟨earlier, earlierObs, by rw [seenLength]; omega⟩
  · simpa only [List.append_assoc] using pointR

/-- The return point uses the actual emitting prefix. R is independent of
    the raw count phase after the helper-return tag, so a repeated equal
    machine state cannot substitute a fabricated history. -/
theorem helper_return_point (c : Config) (history : List MachineState)
    (seen : List LookupObservation.Point) (current : MachineState) (world : World)
    (observed : LookupObservation.observe c.rxSection history =
      .ok (seen ++ [LookupObservation.returned "wg_peer_get_maybe_zero" current]))
    (related : R c history (seen ++ [LookupObservation.returned "wg_peer_get_maybe_zero" current]) current world) :
    LookupObservation.MatchesPointsFrom
      (ExecutedCorrespondence.AtPoint (R c) c.rxSection history) seen
      [LookupObservation.returned "wg_peer_get_maybe_zero" current]
      [⟨.returned "wg_peer_get_maybe_zero", world⟩] := by
  obtain ⟨i, localEvents, present, localObs, count, prefixed, emitted⟩ :=
    LookupObservation.observe_locate c.rxSection history _ observed seen.length
      (LookupObservation.returned "wg_peer_get_maybe_zero" current) (by simp)
  have last : (history.take (i+1)).getLast? = some current := by
    rw [List.getLast?_take]
    simp [present, LookupObservation.returned]
  have localR := related.replace_raw_inactive c history (history.take (i+1)) _ current world
    (helperActive_return seen current) last
  apply LookupObservation.MatchesPointsFrom.cons
  · refine ⟨rfl, ⟨i, localEvents, present, localObs, ?_, ?_, ?_, ?_, localR⟩, True.intro⟩
    · simp
    · simpa only [List.length_append, List.length_singleton] using count
    · have size : seen.length+1 =
          (seen ++ [LookupObservation.returned "wg_peer_get_maybe_zero" current]).length := by simp
      rw [size, List.take_length] at prefixed
      exact prefixed
    · rcases emitted with zero | ⟨earlier, observedEarlier, bound⟩
      · exact .inl zero
      · exact .inr ⟨earlier, observedEarlier, by simp; omega⟩
  · exact .nil

private theorem decisions_length (delta : List LookupObservation.Point) (tags : DecisionPoints delta) :
    (delta.filterMap (·.step)).length = delta.length := by
  induction delta with
  | nil => rfl
  | cons point rest ih =>
    obtain ⟨step, emitted, _⟩ := tags point (by simp)
    simp only [List.filterMap_cons, emitted, List.length_cons]
    exact congrArg Nat.succ (ih (fun q member => tags q (by simp [member])))

private theorem worlds_length (world : World) (steps : List Step) :
    (LookupSearch.decisionWorlds world steps).length = steps.length := by
  induction steps generalizing world with
  | nil => rfl
  | cons step rest ih => simpa only [LookupSearch.decisionWorlds, List.length_cons] using congrArg Nat.succ (ih _)

/-- All stuttering cuts before helper RET. Semantic matching is restricted
    from the same completed prefix; physical count facts are supplied by
    the executed phase theorem at each actual raw index. -/
theorem helper_decision_cuts (c : Config) (world : World) (s : MachineState)
    (history tail : List MachineState) (seen delta : List LookupObservation.Point)
    (sourceHistory : List MirrorHistory.Point)
    (related : R c history seen s world)
    (observed : LookupObservation.observe c.rxSection history = .ok seen)
    (full : LookupObservation.observe c.rxSection (history ++ tail) = .ok (seen ++ delta))
    (matched : LookupObservation.MatchesPoints
      (ExecutedCorrespondence.AtPoint (R c) c.rxSection history) seen sourceHistory)
    (fullMatched : LookupObservation.MatchesPoints
      (ExecutedCorrespondence.AtPoint (R c) c.rxSection (history ++ tail))
      (seen ++ delta) (sourceHistory ++ LookupSearch.decisionWorlds world (delta.filterMap (·.step))))
    (aligned : ExecutedCorrespondence.CutsAligned (R c) c.rxSection history sourceHistory)
    (latest : sourceHistory.getLast?.map (·.world) = some world)
    (tags : DecisionPoints delta) (active : helperActive seen = true)
    (noReturn : lastHelperReturn seen = none) (writes : Address → Prop)
    (frames : ∀ state ∈ tail, state.pc ∈ Image.cutPoints → EqualOutside writes s.data.dmem state.data.dmem)
    (bucketApart : ∀ v, project c world = some v → ∀ a, LookupBucketBytes c v a → ¬writes a)
    (ownerApart : ∀ a, LookupOwnerBytes c a → ¬writes a)
    (countAt : ∀ i current, (history ++ tail)[i]? = some current → history.length ≤ i →
      current.pc ∈ Image.cutPoints → ∀ events, helperActive events = true →
      ∀ v, project c world = some v → ∀ pid count,
      c.focus.peer = some pid → v.count = some count →
      PeerCountPhase.At (countPhase ((history ++ tail).take (i+1)) events) current.data.dmem
        (c.peers pid + .ofNat 64 Layouts.peer_refcount) count) :
    ExecutedCorrespondence.CutsAligned (R c) c.rxSection (history ++ tail)
      (sourceHistory ++ LookupSearch.decisionWorlds world (delta.filterMap (·.step))) := by
  intro i current present cut
  by_cases old : i < history.length
  · have prior : history[i]? = some current := by
      simpa only [List.getElem?_append_left old] using present
    have result := (aligned.append_source (LookupSearch.decisionWorlds world (delta.filterMap (·.step))))
      i current prior cut
    simpa only [List.take_append_of_le_length (by omega : i+1 ≤ history.length)] using result
  · have later : history.length ≤ i := by omega
    let middle := tail.take (i+1-history.length)
    let rest := tail.drop (i+1-history.length)
    have restored : history ++ middle ++ rest = history ++ tail := by
      simp only [middle, rest, List.append_assoc, List.take_append_drop]
    have rawPrefix : (history ++ tail).take (i+1) = history ++ middle := by
      rw [List.take_append, List.take_of_length_le (by omega)]
    obtain ⟨localDelta, remaining, deltaEq, localObs⟩ :=
      LookupObservation.observe_between c.rxSection history middle rest seen delta observed
        (by simpa only [restored] using full)
    have localTags : DecisionPoints localDelta := by
      intro point member
      apply tags point
      rw [deltaEq]
      exact List.mem_append.mpr (.inl member)
    have prefixMatched := ExecutedCorrespondence.prefix_matched
      (front := history ++ middle) (tail := rest)
      (by simpa only [restored] using fullMatched)
      (by simpa only [restored] using full) localObs
    let sourcePart := sourceHistory ++ LookupSearch.decisionWorlds world (localDelta.filterMap (·.step))
    have takeEq : (sourceHistory ++ LookupSearch.decisionWorlds world (delta.filterMap (·.step))).take
        (seen ++ localDelta).length = sourcePart := by
      rw [deltaEq, List.filterMap_append, LookupSearch.decisionWorlds_append, ← List.append_assoc]
      have lengthEq : (seen ++ localDelta).length = sourcePart.length := by
        simp only [sourcePart, List.length_append, worlds_length, decisions_length _ localTags, matched.length_eq]
      rw [lengthEq, List.take_left]
    have inTail : current ∈ tail := by
      apply List.mem_of_getElem?
      simpa only [List.getElem?_append_right later] using present
    have last : (history ++ middle).getLast? = some current := by
      rw [← rawPrefix, List.getLast?_take]
      simp [present]
    have activeNow : helperActive (seen ++ localDelta) = true := by
      rw [helperActive_append_decisions _ _ localTags, active]
    have countNow := countAt i current present later cut (seen ++ localDelta) activeNow
    rw [rawPrefix] at countNow
    have currentR := related.advance_count c history (history ++ middle) seen localDelta s current world
      last localTags noReturn writes (frames current inTail cut) bucketApart ownerApart countNow
    have latestWorld := LookupSearch.latest_world sourceHistory world latest (localDelta.filterMap (·.step))
    change sourcePart.getLast?.map (·.world) = _ at latestWorld
    cases lastPoint : sourcePart.getLast? with
    | none => rw [lastPoint] at latestWorld; cases latestWorld
    | some point =>
      rw [lastPoint] at latestWorld
      have worldEq : point.world = LookupSearch.advance world (localDelta.filterMap (·.step)) :=
        Option.some.inj latestWorld
      exact ⟨seen ++ localDelta, point,
        by simpa only [rawPrefix] using localObs,
        by simpa only [rawPrefix] using prefixMatched,
        by simpa only [takeEq] using lastPoint,
        by simpa only [rawPrefix, worldEq] using currentR⟩

/-- Append the actual RET successor and its committed source world to
    already related interior decisions/cuts. -/
theorem helper_return_compose (c : Config) (front : List MachineState)
    (seen : List LookupObservation.Point) (source : List MirrorHistory.Point)
    (current : MachineState) (world : World)
    (matched : LookupObservation.MatchesPoints
      (ExecutedCorrespondence.AtPoint (R c) c.rxSection front) seen source)
    (aligned : ExecutedCorrespondence.CutsAligned (R c) c.rxSection front source)
    (observed : LookupObservation.observe c.rxSection (front ++ [current]) =
      .ok (seen ++ [LookupObservation.returned "wg_peer_get_maybe_zero" current]))
    (related : R c (front ++ [current])
      (seen ++ [LookupObservation.returned "wg_peer_get_maybe_zero" current]) current world) :
    LookupObservation.MatchesPoints
      (ExecutedCorrespondence.AtPoint (R c) c.rxSection (front ++ [current]))
      (seen ++ [LookupObservation.returned "wg_peer_get_maybe_zero" current])
      (source ++ [⟨.returned "wg_peer_get_maybe_zero", world⟩]) ∧
    ExecutedCorrespondence.CutsAligned (R c) c.rxSection (front ++ [current])
      (source ++ [⟨.returned "wg_peer_get_maybe_zero", world⟩]) := by
  have returned := helper_return_point c (front ++ [current]) seen current world observed related
  have all := (ExecutedCorrespondence.matched_append_history matched [current]).append
    (by simpa only [List.nil_append] using returned)
  refine ⟨all, (aligned.append_source [⟨.returned "wg_peer_get_maybe_zero", world⟩]).snoc current ?_⟩
  intro _
  have lengths := all.length_eq
  refine ⟨_, ⟨.returned "wg_peer_get_maybe_zero", world⟩, observed, ?_, ?_, related⟩
  · refine ⟨by omega, ?_⟩
    rw [lengths, List.take_length]
    exact all
  · rw [lengths, List.take_length]
    simp

#print axioms helper_return_compose
#print axioms helper_decision_cuts
#print axioms helper_return_point
#print axioms helper_decision_points
end Binary.LookupRelation
