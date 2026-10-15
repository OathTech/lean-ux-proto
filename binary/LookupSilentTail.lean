import LookupTailCallback
import LookupReturnSimulation

namespace Binary.LookupRelation
open Leanux Leanux.WG TrustBase LookupHistory LookupObservation
local instance : Labels := Image.linkedLabels

/-- A silent actual suffix extends the same accepted prefix. Only its
    physical footprint, including each anchored cut, must be discharged. -/
theorem silent_suffix (c : Config) (world : World) (s t : MachineState)
    (history tail : List MachineState) (seen : List Point) (source : List MirrorHistory.Point)
    (related : R c history seen s world)
    (observed : observe c.rxSection history = .ok seen)
    (full : observe c.rxSection (history ++ tail) = .ok seen)
    (matched : MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection history) seen source)
    (aligned : ExecutedCorrespondence.CutsAligned (R c) c.rxSection history source)
    (latest : source.getLast?.map (·.world) = some world)
    (inactive : helperActive seen = false) (noReturn : lastHelperReturn seen = none)
    (last : (history ++ tail).getLast? = some t)
    (writes : Address → Prop)
    (frames : ∀ q ∈ tail, q.pc ∈ Image.cutPoints → EqualOutside writes s.data.dmem q.data.dmem)
    (frame : EqualOutside writes s.data.dmem t.data.dmem)
    (apart : ∀ v, project c world = some v → ∀ a, Reads c v a → ¬writes a) :
    MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection (history ++ tail)) seen source ∧
    ExecutedCorrespondence.CutsAligned (R c) c.rxSection (history ++ tail) source ∧
    R c (history ++ tail) seen t world := by
  have cuts := bucket_cuts c world s history tail seen [] source related observed
    (by simpa only [List.append_nil] using full) matched aligned latest
    (by intro p member; cases member) (by intro p member; cases member) inactive noReturn writes frames apart
  exact ⟨ExecutedCorrespondence.matched_append_history matched tail,
    by simpa only [List.filterMap_nil, LookupSearch.decisionWorlds, List.append_nil] using cuts,
    related.frame_inactive_world c world history (history ++ tail) seen seen s t last inactive inactive
      noReturn noReturn rfl writes frame apart⟩

/-- The miss/dead result clear is an actual XOR EBX, preserving every
    undefined AF successor and the current source world. -/
theorem clear_simulation (fetch : Int64 → Option Decoded) (agree : AnchoredDecoderAgreement fetch)
    (c : Config) (world : World) (s : MachineData)
    (history : List MachineState) (seen : List Point) (source : List MirrorHistory.Point)
    (related : R c history seen ⟨s, Image.Lookup.entry+0x71⟩ world)
    (observed : observe c.rxSection history = .ok seen)
    (matched : MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection history) seen source)
    (aligned : ExecutedCorrespondence.CutsAligned (R c) c.rxSection history source)
    (latest : source.getLast?.map (·.world) = some world)
    (inactive : helperActive seen = false) (noReturn : lastHelperReturn seen = none) :
    historySteps fetch 1 (fun final => ∃ af,
      final.machine = ⟨PeerGet.zeroed s (.low .rbx .W32) af, Image.Lookup.entry+0x73⟩ ∧
      final.history = history ++ [final.machine] ∧
      observe c.rxSection final.history = .ok seen ∧
      MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection final.history) seen source ∧
      ExecutedCorrespondence.CutsAligned (R c) c.rxSection final.history source ∧
      R c final.history seen final.machine world)
      ⟨⟨s, Image.Lookup.entry+0x71⟩, history⟩ := by
  apply historySteps_mono fetch 1 _ _ _ _
    (PeerGet.xor32_history fetch (Image.Lookup.entry+0x71) 2 (.low .rbx .W32) (by decide)
      (agree _ _ (by rfl)) s history)
  rintro final ⟨af, machine, recorded⟩
  have machine' : final.machine = ⟨PeerGet.zeroed s (.low .rbx .W32) af, Image.Lookup.entry+0x73⟩ := machine
  have full : observe c.rxSection (history ++ [final.machine]) = .ok seen := by
    have h := observe_snoc c.rxSection history _ final.machine seen [] related.1 observed (by
      simp [LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
    simpa only [List.append_nil] using h
  have composed := silent_suffix c world _ final.machine history [final.machine] seen source related observed full
    matched aligned latest inactive noReturn (by simp) (fun _ => False)
    (by intro q member _; simp only [List.mem_singleton] at member; subst q; rw [machine']; intro a _; rfl)
    (by rw [machine']; intro a _; rfl) (by intro v projected a read; simp)
  exact ⟨af, machine', recorded, by simpa only [recorded] using full, by simpa only [recorded] using composed⟩

/-- The live out-parameter store and its jump preserve R and the accepted
    source prefix when the original entry's output separation is supplied. -/
theorem output_simulation (fetch : Int64 → Option Decoded) (agree : AnchoredDecoderAgreement fetch)
    (c : Config) (world : World) (s : MachineData)
    (history : List MachineState) (seen : List Point) (source : List MirrorHistory.Point)
    (related : R c history seen ⟨s, Image.Lookup.entry+0xca⟩ world)
    (observed : observe c.rxSection history = .ok seen)
    (matched : MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection history) seen source)
    (aligned : ExecutedCorrespondence.CutsAligned (R c) c.rxSection history source)
    (latest : source.getLast?.map (·.world) = some world)
    (inactive : helperActive seen = false) (noReturn : lastHelperReturn seen = none)
    (mapped : (s.dmem.loadInt s.regs.r13.toBitVec 8).isSome = true)
    (apart : ∀ v, project c world = some v → ∀ a, Reads c v a → ¬InRange s.regs.r13.toBitVec 8 a) :
    historySteps fetch 2 (fun final =>
      final.machine = ⟨outputStored s, Image.Lookup.entry+0x73⟩ ∧
      final.history = history ++ [⟨outputStored s, Image.Lookup.entry+0xce⟩, final.machine] ∧
      observe c.rxSection final.history = .ok seen ∧
      MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection final.history) seen source ∧
      ExecutedCorrespondence.CutsAligned (R c) c.rxSection final.history source ∧
      R c final.history seen final.machine world)
      ⟨⟨s, Image.Lookup.entry+0xca⟩, history⟩ := by
  apply historySteps_mono fetch 2 _ _ _ _ (output_history fetch agree s mapped history)
  rintro final ⟨machine, recorded⟩
  let middle : MachineState := ⟨outputStored s, Image.Lookup.entry+0xce⟩
  have first : observe c.rxSection (history ++ [middle]) = .ok seen := by
    have h := observe_snoc c.rxSection history _ middle seen [] related.1 observed (by
      simp [LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
    simpa only [List.append_nil] using h
  have full : observe c.rxSection (history ++ [middle, final.machine]) = .ok seen := by
    have h := observe_snoc c.rxSection (history ++ [middle]) middle final.machine seen [] (by simp) first (by
      simp [middle, LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
    simpa only [List.append_nil, List.append_assoc, List.singleton_append] using h
  have composed := silent_suffix c world _ final.machine history [middle, final.machine] seen source related observed full
    matched aligned latest inactive noReturn (by simp) (InRange s.regs.r13.toBitVec 8)
    (by
      intro q member _
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact output_frame s
      · rw [machine]; exact output_frame s)
    (by rw [machine]; exact output_frame s) apart
  exact ⟨machine, recorded, by simpa only [recorded, middle] using full,
    by simpa only [recorded, middle] using composed⟩

#print axioms silent_suffix
#print axioms clear_simulation
#print axioms output_simulation
end Binary.LookupRelation
