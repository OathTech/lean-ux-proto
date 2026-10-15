import LookupReturnHistory
import LookupRelation
import ExecutedCorrespondence

namespace Binary.LookupRelation
open Leanux Leanux.WG TrustBase LookupHistory LookupObservation
local instance : Labels := Image.linkedLabels

/-- Inactive lookup frames use the current physical memory. A return PC may
    coincide with an anchored pending-store PC; its actual event phase still
    rules that pending state out. -/
theorem R.frame_inactive_world (c : Config) (world : World)
    (raw raw' : List MachineState) (seen seen' : List Point) (s t : MachineState)
    (related : R c raw seen s world) (last : raw'.getLast? = some t)
    (inactive : helperActive seen = false) (inactive' : helperActive seen' = false)
    (noReturn : lastHelperReturn seen = none) (noReturn' : lastHelperReturn seen' = none)
    (sameSteps : seen'.filterMap (·.step) = seen.filterMap (·.step))
    (writes : Address → Prop) (frame : EqualOutside writes s.data.dmem t.data.dmem)
    (apart : ∀ v, project c world = some v → ∀ a, Reads c v a → ¬writes a) :
    R c raw' seen' t world := by
  obtain ⟨_, ⟨v, projected, physical⟩, steps⟩ := related
  refine ⟨last, ⟨v, projected, physical.frame_inactive c raw raw' seen seen' s t v
    inactive inactive' (ownerPending_none _ _ noReturn) (ownerPending_none _ _ noReturn') writes frame
    (apart v projected)⟩, ?_⟩
  exact ⟨by rw [sameSteps]; exact steps.1, steps.2⟩

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

private theorem outer_return_point (c : Config) (history : List MachineState) (seen : List Point)
    (current : MachineState) (world : World)
    (before : observe c.rxSection history = .ok seen)
    (after : observe c.rxSection (history ++ [current]) =
      .ok (seen ++ [returned "wg_index_hashtable_lookup" current]))
    (related : R c (history ++ [current]) (seen ++ [returned "wg_index_hashtable_lookup" current]) current world) :
    MatchesPointsFrom (ExecutedCorrespondence.AtPoint (R c) c.rxSection (history ++ [current])) seen
      [returned "wg_index_hashtable_lookup" current] [⟨.returned "wg_index_hashtable_lookup", world⟩] := by
  refine .cons ⟨rfl, ?_, True.intro⟩ .nil
  refine ⟨history.length, seen ++ [returned "wg_index_hashtable_lookup" current], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [returned]
  · simpa only [show history.length+1 = (history ++ [current]).length by simp, List.take_length] using after
  · simp
  · exact Nat.le_refl _
  · rw [List.take_length]
  · exact .inr ⟨seen, by simpa only [List.take_left] using before, by simp⟩
  · simpa only [show history.length+1 = (history ++ [current]).length by simp, List.take_length, returned] using related

/-- Seven actual epilogue instructions, with R at every saved-register cut
    and the actual outer return marker. The return destination is unrestricted. -/
theorem return_simulation (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (c : Config) (world : World)
    (s : MachineData) (history : List MachineState) (seen : List Point) (source : List MirrorHistory.Point)
    (related : R c history seen ⟨s, Image.Lookup.entry+0x89⟩ world)
    (observed : observe c.rxSection history = .ok seen)
    (matched : MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection history) seen source)
    (aligned : ExecutedCorrespondence.CutsAligned (R c) c.rxSection history source)
    (latest : source.getLast?.map (·.world) = some world)
    (inactive : helperActive seen = false) (noReturn : lastHelperReturn seen = none)
    (bx bp r12 r13 r14 ra : UInt64)
    (h0 : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some (bx.toNat : Int))
    (h1 : s.dmem.loadInt (s.regs.rsp.toBitVec+8#64) 8 = some (bp.toNat : Int))
    (h2 : s.dmem.loadInt (s.regs.rsp.toBitVec+16#64) 8 = some (r12.toNat : Int))
    (h3 : s.dmem.loadInt (s.regs.rsp.toBitVec+24#64) 8 = some (r13.toNat : Int))
    (h4 : s.dmem.loadInt (s.regs.rsp.toBitVec+32#64) 8 = some (r14.toNat : Int))
    (h5 : s.dmem.loadInt (s.regs.rsp.toBitVec+40#64) 8 = some (ra.toNat : Int)) :
    historySteps fetch 7 (fun final =>
      final.machine = ⟨LookupReturn.restoreData s bx bp r12 r13 r14 6, .ofBitVec ra.toBitVec⟩ ∧
      final.history = history ++ LookupReturn.restoreStates s bx bp r12 r13 r14 ra ∧
      observe c.rxSection final.history = .ok (seen ++ [returned "wg_index_hashtable_lookup" final.machine]) ∧
      MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection final.history)
        (seen ++ [returned "wg_index_hashtable_lookup" final.machine]) (source ++ [⟨.returned "wg_index_hashtable_lookup", world⟩]) ∧
      ExecutedCorrespondence.CutsAligned (R c) c.rxSection final.history (source ++ [⟨.returned "wg_index_hashtable_lookup", world⟩]) ∧
      R c final.history (seen ++ [returned "wg_index_hashtable_lookup" final.machine]) final.machine world)
      ⟨⟨s, Image.Lookup.entry+0x89⟩, history⟩ := by
  apply historySteps_mono fetch 7 _ _ _ _ (LookupReturn.epilogue_history fetch agree s history bx bp r12 r13 r14 ra h0 h1 h2 h3 h4 h5)
  rintro final ⟨machine, recorded⟩
  let p1 : MachineState := ⟨LookupReturn.restoreData s bx bp r12 r13 r14 0, Image.Lookup.entry+0x8c⟩
  let p2 : MachineState := ⟨LookupReturn.restoreData s bx bp r12 r13 r14 1, Image.Lookup.entry+0x8d⟩
  let p3 : MachineState := ⟨LookupReturn.restoreData s bx bp r12 r13 r14 2, Image.Lookup.entry+0x8e⟩
  let p4 : MachineState := ⟨LookupReturn.restoreData s bx bp r12 r13 r14 3, Image.Lookup.entry+0x90⟩
  let p5 : MachineState := ⟨LookupReturn.restoreData s bx bp r12 r13 r14 4, Image.Lookup.entry+0x92⟩
  let p6 : MachineState := ⟨LookupReturn.restoreData s bx bp r12 r13 r14 5, Image.Lookup.entry+0x94⟩
  let p7 : MachineState := ⟨LookupReturn.restoreData s bx bp r12 r13 r14 6, .ofBitVec ra.toBitVec⟩
  let raw1 := history ++ [p1]
  let raw2 := raw1 ++ [p2]
  let raw3 := raw2 ++ [p3]
  let raw4 := raw3 ++ [p4]
  let raw5 := raw4 ++ [p5]
  let raw6 := raw5 ++ [p6]
  let raw7 := raw6 ++ [p7]
  have obs1 : observe c.rxSection raw1 = .ok seen := by
    have h := observe_snoc c.rxSection history ⟨s, Image.Lookup.entry+0x89⟩ p1 seen [] related.1 observed (by
      simp [p1, LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
    simpa only [List.append_nil] using h
  have r1 := related.frame_inactive_world c world history raw1 seen seen _ p1 (by simp [raw1]) inactive inactive
    noReturn noReturn rfl (fun _ => False) (by intro a _; rfl) (by intro v projected a read; simp)
  have cuts1 := silent_snoc c history seen source world p1 obs1 matched aligned latest r1
  have obs2 : observe c.rxSection raw2 = .ok seen := by
    have h := observe_snoc c.rxSection raw1 p1 p2 seen [] (by simp [raw1]) obs1 (by
      simp [p1, p2, LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
    simpa only [List.append_nil] using h
  have r2 := related.frame_inactive_world c world history raw2 seen seen _ p2 (by simp [raw2]) inactive inactive
    noReturn noReturn rfl (fun _ => False) (by intro a _; rfl) (by intro v projected a read; simp)
  have cuts2 := silent_snoc c raw1 seen source world p2 obs2 cuts1.1 cuts1.2 latest r2
  have obs3 : observe c.rxSection raw3 = .ok seen := by
    have h := observe_snoc c.rxSection raw2 p2 p3 seen [] (by simp [raw2]) obs2 (by
      simp [p2, p3, LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
    simpa only [List.append_nil] using h
  have r3 := related.frame_inactive_world c world history raw3 seen seen _ p3 (by simp [raw3]) inactive inactive
    noReturn noReturn rfl (fun _ => False) (by intro a _; rfl) (by intro v projected a read; simp)
  have cuts3 := silent_snoc c raw2 seen source world p3 obs3 cuts2.1 cuts2.2 latest r3
  have obs4 : observe c.rxSection raw4 = .ok seen := by
    have h := observe_snoc c.rxSection raw3 p3 p4 seen [] (by simp [raw3]) obs3 (by
      simp [p3, p4, LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
    simpa only [List.append_nil] using h
  have r4 := related.frame_inactive_world c world history raw4 seen seen _ p4 (by simp [raw4]) inactive inactive
    noReturn noReturn rfl (fun _ => False) (by intro a _; rfl) (by intro v projected a read; simp)
  have cuts4 := silent_snoc c raw3 seen source world p4 obs4 cuts3.1 cuts3.2 latest r4
  have obs5 : observe c.rxSection raw5 = .ok seen := by
    have h := observe_snoc c.rxSection raw4 p4 p5 seen [] (by simp [raw4]) obs4 (by
      simp [p4, p5, LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
    simpa only [List.append_nil] using h
  have r5 := related.frame_inactive_world c world history raw5 seen seen _ p5 (by simp [raw5]) inactive inactive
    noReturn noReturn rfl (fun _ => False) (by intro a _; rfl) (by intro v projected a read; simp)
  have cuts5 := silent_snoc c raw4 seen source world p5 obs5 cuts4.1 cuts4.2 latest r5
  have obs6 : observe c.rxSection raw6 = .ok seen := by
    have h := observe_snoc c.rxSection raw5 p5 p6 seen [] (by simp [raw5]) obs5 (by
      simp [p5, p6, LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
    simpa only [List.append_nil] using h
  have r6 := related.frame_inactive_world c world history raw6 seen seen _ p6 (by simp [raw6]) inactive inactive
    noReturn noReturn rfl (fun _ => False) (by intro a _; rfl) (by intro v projected a read; simp)
  have cuts6 := silent_snoc c raw5 seen source world p6 obs6 cuts5.1 cuts5.2 latest r6
  have obs7 : observe c.rxSection raw7 = .ok (seen ++ [returned "wg_index_hashtable_lookup" p7]) :=
    observe_snoc c.rxSection raw6 p6 p7 seen _ (by simp [raw6]) obs6 (by
      simp [p6, p7, LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
  have inactive' : helperActive (seen ++ [returned "wg_index_hashtable_lookup" p7]) = false := by
    simpa [helperActive, helperTag, returned] using inactive
  have r7 := related.frame_inactive_world c world history raw7 seen (seen ++ [returned "wg_index_hashtable_lookup" p7]) _ p7
    (by simp [raw7]) inactive inactive' noReturn (by simp [lastHelperReturn, returned]) (by simp [returned])
    (fun _ => False) (by intro a _; rfl) (by intro v projected a read; simp)
  have point := outer_return_point c raw6 seen p7 world obs6 obs7 r7
  have allMatched := (ExecutedCorrespondence.matched_append_history cuts6.1 [p7]).append
    (by simpa only [List.nil_append] using point)
  have allCuts := (cuts6.2.append_source [⟨.returned "wg_index_hashtable_lookup", world⟩]).snoc p7 (by
    intro _
    have sizes := allMatched.length_eq
    refine ⟨_, ⟨.returned "wg_index_hashtable_lookup", world⟩, obs7, ?_, ?_, r7⟩
    · refine ⟨by omega, ?_⟩
      rw [sizes, List.take_length]
      exact allMatched
    · rw [sizes, List.take_length]
      simp)
  refine ⟨machine, recorded, ?_, ?_, ?_, ?_⟩
  all_goals simp only [recorded, machine]
  · simpa only [raw7, raw6, raw5, raw4, raw3, raw2, raw1, p1, p2, p3, p4, p5, p6, p7, LookupReturn.restoreStates, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using obs7
  · simpa only [raw7, raw6, raw5, raw4, raw3, raw2, raw1, p1, p2, p3, p4, p5, p6, p7, LookupReturn.restoreStates, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using allMatched
  · simpa only [raw7, raw6, raw5, raw4, raw3, raw2, raw1, p1, p2, p3, p4, p5, p6, p7, LookupReturn.restoreStates, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using allCuts
  · simpa only [raw7, raw6, raw5, raw4, raw3, raw2, raw1, p1, p2, p3, p4, p5, p6, p7, LookupReturn.restoreStates, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using r7

#print axioms R.frame_inactive_world
#print axioms return_simulation
end Binary.LookupRelation
