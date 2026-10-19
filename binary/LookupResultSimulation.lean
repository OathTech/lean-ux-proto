import LookupResultRelation
import ExecutedCorrespondence

namespace Binary.LookupRelation
open Leanux Leanux.WG TrustBase LookupHistory LookupObservation
local instance : Labels := Image.linkedLabels

private theorem silent_snoc (c : Config) (history : List MachineState)
    (seen : List Point) (source : List MirrorHistory.Point) (world : World) (current : MachineState)
    (observed : observe c.rxSection (history ++ [current]) = .ok seen)
    (matched : MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection history) seen source)
    (aligned : ExecutedCorrespondence.CutsAligned (R c) c.rxSection history source)
    (latest : source.getLast?.map (·.world) = some world)
    (related : R c (history ++ [current]) seen current world) :
    MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection (history ++ [current])) seen source ∧
    ExecutedCorrespondence.CutsAligned (R c) c.rxSection (history ++ [current]) source := by
  have extended := ExecutedCorrespondence.matched_append_history matched [current]
  refine ⟨extended, aligned.snoc current ?_⟩
  intro _
  cases last : source.getLast? with
  | none => rw [last] at latest; cases latest
  | some point =>
    have worldEq : point.world = world := by rw [last] at latest; exact Option.some.inj latest
    refine ⟨seen, point, observed, ?_, ?_, ?_⟩
    · refine ⟨by rw [matched.length_eq]; exact Nat.le_refl _, ?_⟩
      simpa only [matched.length_eq, List.take_length] using extended
    · simpa only [matched.length_eq, List.take_length] using last
    · simpa only [worldEq] using related

private theorem result_point (c : Config) (history : List MachineState) (seen : List Point)
    (current : MachineState) (world : World) (outcome : Bool)
    (before : observe c.rxSection history = .ok seen)
    (after : observe c.rxSection (history ++ [current]) =
      .ok (seen ++ [decision c.rxSection .idxPeerAlive outcome current]))
    (related : R c (history ++ [current]) (seen ++ [decision c.rxSection .idxPeerAlive outcome current]) current
      (LookupMirror.record world .idxPeerAlive outcome)) :
    MatchesPointsFrom (ExecutedCorrespondence.AtPoint (R c) c.rxSection (history ++ [current])) seen
      [decision c.rxSection .idxPeerAlive outcome current]
      [⟨.decision .idxPeerAlive, LookupMirror.record world .idxPeerAlive outcome⟩] := by
  refine .cons ⟨rfl, ?_, ?_⟩ .nil
  · refine ⟨history.length, seen ++ [decision c.rxSection .idxPeerAlive outcome current], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [decision]
    · simpa only [show history.length+1 = (history ++ [current]).length by simp, List.take_length] using after
    · simp
    · exact Nat.le_refl _
    · rw [List.take_length]
    · exact .inr ⟨seen, by simpa only [List.take_left] using before, by simp⟩
    · simpa only [show history.length+1 = (history ++ [current]).length by simp, List.take_length, decision] using related
  · have rx : world.netRxSection = c.rxSection := related.2.2.2
    simp [decision, LookupMirror.record, rx]

/-- Actual MOV/MOV/TEST/Jcc result region, preserving all three pending
    cuts and committing the landed owner setter at idxPeerAlive. -/
theorem result_simulation (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (c : Config) (world setWorld : World)
    (s : MachineData) (history : List MachineState) (seen : List Point)
    (source : List MirrorHistory.Point)
    (related : R c history seen ⟨s, Image.Lookup.entry+0xba⟩ world)
    (observed : observe c.rxSection history = .ok seen)
    (matched : MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection history) seen source)
    (aligned : ExecutedCorrespondence.CutsAligned (R c) c.rxSection history source)
    (latest : source.getLast?.map (·.world) = some world)
    (returned : lastHelperReturn seen = some ⟨s, Image.Lookup.entry+0xba⟩)
    (owner : IndexOwner) (focused : c.focus.owner = some owner)
    (word : Option PeerId) (result : s.regs.rax.toBitVec = OwnerWord.pointer c.peers word)
    (location : s.regs.rbx.toBitVec = ownerAddress c owner)
    (setRun : (Source.setPeerWord owner word).run world = .ok ((), setWorld))
    (bucketApart : ∀ v, project c world = some v → ∀ a, LookupBucketBytes c v a →
      ¬InRange (ownerAddress c owner) 8 a)
    (countApart : ∀ a, LookupCountBytes c a → ¬InRange (ownerAddress c owner) 8 a) :
    historySteps fetch 4 (fun final => ∃ af,
      final.machine = resultExit s af ∧ final.history = history ++ resultStates s af ∧
      observe c.rxSection final.history =
        .ok (seen ++ [decision c.rxSection .idxPeerAlive (decide (s.regs.rax ≠ 0)) final.machine]) ∧
      MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection final.history)
        (seen ++ [decision c.rxSection .idxPeerAlive (decide (s.regs.rax ≠ 0)) final.machine])
        (source ++ [⟨.decision .idxPeerAlive, LookupMirror.record setWorld .idxPeerAlive (decide (s.regs.rax ≠ 0))⟩]) ∧
      ExecutedCorrespondence.CutsAligned (R c) c.rxSection final.history
        (source ++ [⟨.decision .idxPeerAlive, LookupMirror.record setWorld .idxPeerAlive (decide (s.regs.rax ≠ 0))⟩]) ∧
      R c final.history (seen ++ [decision c.rxSection .idxPeerAlive (decide (s.regs.rax ≠ 0)) final.machine])
        final.machine (LookupMirror.record setWorld .idxPeerAlive (decide (s.regs.rax ≠ 0))))
      ⟨⟨s, Image.Lookup.entry+0xba⟩, history⟩ := by
  obtain ⟨v, projected, physical⟩ := related.2.1
  have ownerField := physical.2.2.1
  simp only [focused] at ownerField
  obtain ⟨old, _, oldField⟩ := ownerField
  have ordinary : ownerPending seen ⟨s, Image.Lookup.entry+0xba⟩ = none := by
    simp only [ownerPending]
    rw [if_neg (by decide)]
  simp only [OwnerFieldAt, ordinary] at oldField
  have field : OwnerWord.Field c.peers s.dmem s.regs.rbx.toBitVec old := by simpa only [location] using oldField
  apply historySteps_mono fetch 4 _ _ _ _ (result_history fetch agree c.peers s old field history)
  rintro final ⟨af, machine, recorded⟩
  let p1 : MachineState := ⟨OwnerWord.stored s, Image.Lookup.entry+0xbd⟩
  let p2 : MachineState := ⟨resultSaved s, Image.Lookup.entry+0xc0⟩
  let p3 : MachineState := ⟨tested (.low .rax .W64) (resultSaved s) af, Image.Lookup.entry+0xc3⟩
  let p4 := resultExit s af
  let h1 := history ++ [p1]
  let h2 := h1 ++ [p2]
  let h3 := h2 ++ [p3]
  let h4 := h3 ++ [p4]
  have obs1 : observe c.rxSection h1 = .ok seen := by
    have h := observe_snoc c.rxSection history ⟨s, Image.Lookup.entry+0xba⟩ p1 seen [] related.1 observed (by
      simp [p1, LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
    simpa only [List.append_nil] using h
  have obs2 : observe c.rxSection h2 = .ok seen := by
    have h := observe_snoc c.rxSection h1 p1 p2 seen [] (by simp [h1]) obs1 (by
      simp [p1, p2, LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
    simpa only [List.append_nil] using h
  have obs3 : observe c.rxSection h3 = .ok seen := by
    have h := observe_snoc c.rxSection h2 p2 p3 seen [] (by simp [h2]) obs2 (by
      simp [p2, p3, LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
    simpa only [List.append_nil] using h
  have obs4 : observe c.rxSection h4 = .ok (seen ++ [decision c.rxSection .idxPeerAlive (decide (s.regs.rax ≠ 0)) p4]) :=
    observe_snoc c.rxSection h3 p3 p4 seen _ (by simp [h3]) obs3 (by
      by_cases zero : s.regs.rax = 0 <;>
        simp [p3, p4, resultExit, resultSaved, OwnerWord.stored, tested, LookupObservation.edge,
          LookupObservation.choice, Image.Lookup.entry, Image.PeerGet.entry, zero] <;> rfl)
  have r1 := related.result_pending c world s history h1 seen returned owner focused location bucketApart countApart af p1
    (by simp [p1, resultStates]) (by exact .inl rfl) (by simp [h1])
  have r2 := related.result_pending c world s history h2 seen returned owner focused location bucketApart countApart af p2
    (by simp [p2, resultStates]) (by exact .inr (.inl rfl)) (by simp [h2])
  have r3 := related.result_pending c world s history h3 seen returned owner focused location bucketApart countApart af p3
    (by simp [p3, resultStates]) (by exact .inr (.inr rfl)) (by simp [h3])
  have r4 := related.result_committed c world setWorld s history h4 seen returned owner focused word result location setRun
    bucketApart countApart af (by simp [h4, p4])
  have first := silent_snoc c history seen source world p1 obs1 matched aligned latest r1
  have second := silent_snoc c h1 seen source world p2 obs2 first.1 first.2 latest r2
  have third := silent_snoc c h2 seen source world p3 obs3 second.1 second.2 latest r3
  have point := result_point c h3 seen p4 setWorld (decide (s.regs.rax ≠ 0)) obs3 obs4 r4
  have allMatched := (ExecutedCorrespondence.matched_append_history third.1 [p4]).append
    (by simpa only [List.nil_append] using point)
  have allCuts := (third.2.append_source [⟨.decision .idxPeerAlive, LookupMirror.record setWorld .idxPeerAlive (decide (s.regs.rax ≠ 0))⟩]).snoc p4 (by
    intro _
    have sizes := allMatched.length_eq
    refine ⟨_, ⟨.decision .idxPeerAlive, LookupMirror.record setWorld .idxPeerAlive (decide (s.regs.rax ≠ 0))⟩, obs4, ?_, ?_, r4⟩
    · refine ⟨by omega, ?_⟩
      rw [sizes, List.take_length]
      exact allMatched
    · rw [sizes, List.take_length]
      simp)
  refine ⟨af, machine, recorded, ?_, ?_, ?_, ?_⟩
  all_goals simp only [recorded, machine]
  · simpa only [h4, h3, h2, h1, p1, p2, p3, p4, resultStates, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using obs4
  · simpa only [h4, h3, h2, h1, p1, p2, p3, p4, resultStates, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using allMatched
  · simpa only [h4, h3, h2, h1, p1, p2, p3, p4, resultStates, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using allCuts
  · simpa only [h4, h3, h2, h1, p1, p2, p3, p4, resultStates, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using r4

#print axioms result_simulation
end Binary.LookupRelation
