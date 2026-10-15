import CommonBitsSegments
import CommonBitsBodyState
import AllowedipsLoopFrame

namespace Binary.CommonBits
open TrustBase LookupObservation
local instance : Labels := Image.linkedLabels

abbrev EventView := MirrorHistory.Tag × Option Leanux.Step

def pointView (p : Point) : EventView := (p.tag, p.step)

/-- Local actual execution, including every intermediate state. The event
    signature is checked against the observer, and cut frames refer to those
    actual states. Service interiors are covered by their no-reentry clauses. -/
structure Local (writes : BitVec 64 → Prop) (initial : MachineState)
    (rxSection : Nat) (signature : List EventView) (final : Executed) : Prop where
  head : final.history.head? = some initial
  last : final.history.getLast? = some final.machine
  observed : ∃ points, observeHistory (AllowedipsObservation.edge rxSection) final.history = .ok points ∧
    points.map pointView = signature
  frame : EqualOutside writes initial.data.dmem final.machine.data.dmem
  cuts : ∀ q ∈ final.history, q.pc ∈ AllowedipsImage.cutPoints →
    EqualOutside writes initial.data.dmem q.data.dmem
  ordinary : ∀ q ∈ final.history.dropLast, PeerCountPhase.Ordinary q

private theorem restore {path : List MachineState} {s : MachineState}
    (last : path.getLast? = some s) : path.dropLast ++ [s] = path :=
  AllowedipsLoop.history_restore last

/-- Composition retains the actual first path and second path at their shared
    physical endpoint. There is no supplied execution history among the premises. -/
theorem Local.trans {writes initial rxSection firstSignature secondSignature first second final}
    (a : Local writes initial rxSection firstSignature first)
    (b : Local writes first.machine rxSection secondSignature second)
    (machine : final.machine = second.machine)
    (recorded : final.history = first.history.dropLast ++ second.history) :
    Local writes initial rxSection (firstSignature ++ secondSignature) final := by
  have firstNE : first.history ≠ [] := by intro h; have hh := a.head; rw [h] at hh; cases hh
  have secondNE : second.history ≠ [] := by intro h; have hh := b.head; rw [h] at hh; cases hh
  obtain ⟨tail, secondPath⟩ : ∃ tail, second.history = first.machine :: tail := by
    cases h : second.history with
    | nil => exact False.elim (secondNE h)
    | cons x tail =>
      have e : x = first.machine := by simpa only [h, List.head?_cons, Option.some.injEq] using b.head
      exact ⟨tail, congrArg (fun z => z :: tail) e⟩
  have joined : final.history = first.history ++ tail := by
    rw [recorded, secondPath, ← List.singleton_append, ← List.append_assoc, restore a.last]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [joined, List.head?_append, a.head]; rfl
  · rw [recorded, List.getLast?_append, b.last, machine]; rfl
  · obtain ⟨p,hp,vp⟩ := a.observed
    obtain ⟨q,hq,vq⟩ := b.observed
    refine ⟨p++q, ?_, by simp only [List.map_append, vp, vq]⟩
    rw [recorded, secondPath, observeHistory_splice, restore a.last, hp, ← secondPath, hq]
    rfl
  · rw [machine]
    intro address outside
    exact (a.frame address outside).trans (b.frame address outside)
  · intro q member cut
    rw [recorded] at member
    rcases List.mem_append.mp member with left | right
    · exact a.cuts q (List.dropLast_subset _ left) cut
    · intro address outside
      exact (a.frame address outside).trans (b.cuts q right cut address outside)
  · intro q member
    rw [recorded, List.dropLast_append_of_ne_nil secondNE] at member
    rcases List.mem_append.mp member with left | right
    · exact a.ordinary q left
    · exact b.ordinary q right

/-- A straight-line scalar segment with no interior cut preserves history,
    observation silence, all required frames and count-scanner neutrality. -/
theorem quiet (fetch : Int64 → Option Decoded) (pc : Int64)
    (code : List (Kraken.Sized Directive)) (layout : LaidOut fetch pc code)
    (s : MachineData) (P : MachineState → Prop) (writes : BitVec 64 → Prop)
    (run : (Directives.interp code s pc (fun p d => .done ⟨d,p⟩)).All
      (fun t => P t ∧ t.data.dmem = s.dmem))
    (rxSection : Nat)
    (silent : ∀ address ∈ AllowedipsLoop.regionPCs pc code, ∀ before after,
      before.pc = address → AllowedipsObservation.edge rxSection before after = .ok [])
    (noInterior : ∀ address ∈ (AllowedipsLoop.regionPCs pc code).tail,
      address ∉ AllowedipsImage.cutPoints)
    (ordinary : ∀ address ∈ AllowedipsLoop.regionPCs pc code,
      address ≠ Image.PeerGet.entry+0xaf ∧ address ≠ Image.PeerGet.entry+0x4a) :
    Eventually (historyStep fetch) (fun t => P t.machine ∧ Local writes ⟨s,pc⟩ rxSection [] t)
      ⟨⟨s,pc⟩,[⟨s,pc⟩]⟩ := by
  have executed := AllowedipsLoop.region_history layout s _ run []
  apply eventually_weaken (historyStep fetch) _ _ _ _ executed
  rintro t ⟨⟨post,memory⟩,path,head,last,recorded,inside⟩
  have eq : t.history = path := by simpa only [List.nil_append] using recorded
  have frame : EqualOutside writes s.dmem t.machine.data.dmem := by rw [memory]; intro _ _; rfl
  refine ⟨post, ?_⟩
  refine ⟨by rw [eq]; exact head, by rw [eq]; exact last, ?_, frame, ?_, ?_⟩
  · refine ⟨[], ?_, rfl⟩
    rw [eq]
    apply AllowedipsLoop.observe_silent
    intro before member after
    exact silent before.pc (inside before member).1 before after rfl
  · intro q member cut
    rw [eq, ← restore last] at member
    rcases List.mem_append.mp member with prior | endpoint
    · rcases (inside q prior).2 with start | interior
      · rw [start]; intro _ _; rfl
      · exact False.elim (noInterior q.pc interior cut)
    · have same : q = t.machine := List.mem_singleton.mp endpoint
      simpa only [same] using frame
  · intro q member
    rw [eq] at member
    exact ordinary q.pc (inside q member).1

/-- Sequential composition on the same actual history and memory footprint. -/
theorem chain (fetch : Int64 → Option Decoded) (writes : BitVec 64 → Prop)
    (initial : MachineState) (rxSection : Nat) (firstSignature secondSignature : List EventView)
    (P Q : MachineState → Prop)
    (first : Eventually (historyStep fetch)
      (fun t => P t.machine ∧ Local writes initial rxSection firstSignature t) ⟨initial,[initial]⟩)
    (next : ∀ middle, P middle → Eventually (historyStep fetch)
      (fun t => Q t.machine ∧ Local writes middle rxSection secondSignature t) ⟨middle,[middle]⟩) :
    Eventually (historyStep fetch)
      (fun t => Q t.machine ∧ Local writes initial rxSection (firstSignature++secondSignature) t)
      ⟨initial,[initial]⟩ := by
  apply eventually_trans (historyStep fetch) _ _ _ first
  rintro middle ⟨post, trace⟩
  have continued := history_prepend fetch _ _ (next middle.machine post) middle.history.dropLast
  rw [restore trace.last] at continued
  apply eventually_weaken (historyStep fetch) _ _ _ _ continued
  rintro final ⟨localState, ⟨result, localTrace⟩, machine, recorded⟩
  exact ⟨machine.symm ▸ result, trace.trans localTrace machine recorded⟩

/-- Every declared M2 correspondence cut is backed by decoded instructions. -/
theorem cut_decoded : ∀ pc ∈ AllowedipsImage.cutPoints,
    (AllowedipsImage.fetch pc).isSome = true := by
  intro pc member
  simp only [AllowedipsImage.cutPoints, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst pc; rfl

end Binary.CommonBits
