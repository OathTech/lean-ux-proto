import PeerPhysicalSimulation
import PeerDecisionCorrespondence

namespace Binary.LookupRelation
open Leanux Leanux.WG LookupObservation PeerCountPhase

/-- The entry call marker is not a helper decision; every helper decision
    observed in a complete lookup history is at an anchored cut. -/
theorem observe_helper_cuts (rx : Nat) (history : List MachineState) (events : List Point)
    (observed : observe rx history = .ok events) :
    ∀ point ∈ events, HelperTag point.tag → point.machine.pc ∈ Image.cutPoints := by
  cases history with
  | nil => cases observed
  | cons first rest =>
    by_cases entry : first.pc = Image.Lookup.entry
    · cases raw : observeHistory (edge rx) (first :: rest) with
      | error error => simp [observe, entry, raw] at observed; cases observed
      | ok delta =>
        simp only [observe, entry, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at observed
        simp only [raw] at observed
        have equal : events = call "wg_index_hashtable_lookup" first :: delta := (Except.ok.inj observed).symm
        subst events
        intro point member tag
        rcases List.mem_cons.mp member with same | later
        · subst point; simp [call, HelperTag] at tag
        · exact observed_helper_cuts rx _ _ raw point later tag
    · simp [observe, entry] at observed; cases observed

/-- All live-helper decisions and stuttering cuts before RET. The physical
    count is derived from the incoming R and the actual successful-CMPXCHG
    phase, while the source worlds are the decision execution itself. -/
theorem live_interior (c : Config) (world : World) (s : MachineState)
    (history middle tail interior : List MachineState) (current : MachineState)
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
    (pid : PeerId) (focused : c.focus.peer = some pid) (old : BitVec 32)
    (phase : IncrementingReturnAt history (history ++ middle) (history ++ middle ++ tail)
      (c.peers pid + .ofNat 64 Layouts.peer_refcount) old)
    (splitHistory : (history ++ interior) ++ [current] = history ++ middle ++ tail)
    (initial : scan none history = none)
    (field : s.data.dmem.loadInt (c.peers pid + .ofNat 64 Layouts.peer_refcount) 4 = some (old.toNat : Int))
    (writes : Address → Prop)
    (apart : ∀ j < 4, ¬writes (c.peers pid + .ofNat 64 Layouts.peer_refcount + .ofNat 64 j))
    (bound : old.toNat+1 < 2^32)
    (oldFrames : ∀ q ∈ middle, q.pc ∈ Image.cutPoints → EqualOutside writes s.data.dmem q.data.dmem)
    (newFrames : ∀ q ∈ tail, q.pc ∈ Image.cutPoints →
      EqualOutside writes (s.data.dmem.storeInt (c.peers pid + .ofNat 64 Layouts.peer_refcount) 4 (old+1).toInt) q.data.dmem)
    (bucketApart : ∀ v, project c world = some v → ∀ a, TrustBase.LookupBucketBytes c v a →
      ¬(InRange (c.peers pid + .ofNat 64 Layouts.peer_refcount) 4 a ∨ writes a))
    (ownerApart : ∀ a, TrustBase.LookupOwnerBytes c a →
      ¬(InRange (c.peers pid + .ofNat 64 Layouts.peer_refcount) 4 a ∨ writes a)) :
    MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection (history ++ interior))
      (seen ++ delta) (sourceHistory ++ LookupSearch.decisionWorlds world (delta.filterMap (·.step))) ∧
    ExecutedCorrespondence.CutsAligned (R c) c.rxSection (history ++ interior)
      (sourceHistory ++ LookupSearch.decisionWorlds world (delta.filterMap (·.step))) := by
  have cuts : ∀ point ∈ delta, point.machine.pc ∈ Image.cutPoints := by
    intro point member
    exact observe_helper_cuts _ _ _ frontObs point (List.mem_append.mpr (.inr member)) (helperTags point member)
  let allWrites := fun a => InRange (c.peers pid + .ofNat 64 Layouts.peer_refcount) 4 a ∨ writes a
  have frames : ∀ q ∈ interior, q.pc ∈ Image.cutPoints → EqualOutside allWrites s.data.dmem q.data.dmem := by
    intro q member cut
    have tails : interior ++ [current] = middle ++ tail := by
      apply List.append_cancel_left (as := history)
      simpa only [List.append_assoc] using splitHistory
    have inAll : q ∈ middle ++ tail := by rw [← tails]; simp [member]
    rcases List.mem_append.mp inAll with before | after
    · intro a outside
      exact oldFrames q before cut a (fun h => outside (.inr h))
    · exact (storeInt_frame s.data.dmem _ 4 (old+1).toInt).trans (newFrames q after cut)
  have counts : ∀ i q, (history ++ interior)[i]? = some q → history.length ≤ i →
      q.pc ∈ Image.cutPoints → ∀ events, helperActive events = true →
      ∀ v, project c world = some v → ∀ other number,
      c.focus.peer = some other → v.count = some number →
      At (countPhase ((history ++ interior).take (i+1)) events) q.data.dmem
        (c.peers other + .ofNat 64 Layouts.peer_refcount) number := by
    intro i q present later cut events activeNow v projected other number focusOther count
    have before := (List.getElem?_eq_some_iff.mp present).1
    have presentFull : (history ++ middle ++ tail)[i]? = some q := by
      rw [← splitHistory, List.getElem?_append_left before]
      exact present
    have proper : i+1 < (history ++ middle ++ tail).length := by
      rw [← splitHistory, List.length_append, List.length_singleton]
      omega
    have result := helper_live_count_related c world s history middle tail seen related pid focused old phase
      initial field writes apart bound oldFrames newFrames i q presentFull later proper cut events activeNow
      v projected other number focusOther count
    simpa only [← splitHistory, List.take_append_of_le_length (by omega : i+1 ≤ (history ++ interior).length)] using result
  have points := helper_decision_points c world s history interior seen delta related observed frontObs tags cuts
    noReturn allWrites frames bucketApart ownerApart (by
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
    matched fullMatched aligned latest tags active noReturn allWrites frames bucketApart ownerApart counts⟩

#print axioms observe_helper_cuts
#print axioms live_interior
end Binary.LookupRelation
