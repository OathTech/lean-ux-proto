import LookupFromPre
import PeerPhysicalSimulation

namespace Binary.LookupRelation
open Leanux Leanux.WG TrustBase LookupHistory LookupObservation PeerCountPhase
local instance : Labels := Image.linkedLabels

/-- Changing the raw/call cursor preserves R when the count scanner is
    still empty and the actual write frame preserves its physical reads. -/
theorem R.frame_no_pending (c : Config) (world : World)
    (history nextHistory : List MachineState) (seen nextSeen : List Point) (s t : MachineState)
    (related : R c history seen s world)
    (last : nextHistory.getLast? = some t)
    (initial : scan none history = none) (nextInitial : scan none nextHistory = none)
    (noReturn : lastHelperReturn seen = none) (nextNoReturn : lastHelperReturn nextSeen = none)
    (sameSteps : nextSeen.filterMap (·.step) = seen.filterMap (·.step))
    (writes : Address → Prop) (frame : EqualOutside writes s.data.dmem t.data.dmem)
    (apart : ∀ v, project c world = some v → ∀ a, Reads c v a → ¬writes a) :
    R c nextHistory nextSeen t world := by
  obtain ⟨_, ⟨v, projected, physical⟩, steps⟩ := related
  refine ⟨last, ⟨v, projected, ?_⟩, ?_⟩
  · refine physical.frame_count c history nextHistory seen nextSeen s t v
      (ownerPending_none _ _ noReturn) (ownerPending_none _ _ nextNoReturn) writes frame ?_ ?_ ?_
    · intro a read
      apply apart v projected a
      rcases read with head | node
      · exact .inl head
      · exact .inr (.inl node)
    · intro a read
      exact apart v projected a (.inr (.inr (.inl read)))
    · intro pid number focused value
      have loaded := R.initial_count c history seen s world ⟨by assumption, ⟨v, projected, physical⟩, steps⟩
        initial v projected pid focused number value
      have noPhase : countPhase nextHistory nextSeen = none := by simp only [countPhase, nextInitial, ite_self]
      rw [noPhase]
      exact At.frame frame (fun j hj => apart v projected _ (.inr (.inr (.inr ⟨pid, focused, j, hj, rfl⟩)))) loaded
  · exact ⟨by rw [sameSteps]; exact steps.1, steps.2⟩

/-- The selected bucket exit first executes its real PC callback. The
    helper's owner-word load starts only at the resulting +b2 cursor. -/
theorem selected_callback (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (tracePc : TracePcContract fetch)
    (c : Config) (world : World) (s : Executed)
    (pc : s.machine.pc = Image.Lookup.entry+0xad)
    (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (ready : LookupCoverage.CallsReady coverage preempt s.machine.data)
    (seen raw : List Point) (source : List MirrorHistory.Point)
    (related : R c s.history seen s.machine world)
    (observed : observe c.rxSection s.history = .ok seen)
    (rawObserved : observeHistory (edge c.rxSection) s.history = .ok raw)
    (matched : MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection s.history) seen source)
    (aligned : ExecutedCorrespondence.CutsAligned (R c) c.rxSection s.history source)
    (latest : source.getLast?.map (·.world) = some world)
    (inactive : helperActive seen = false) (noReturn : lastHelperReturn seen = none)
    (apart : ∀ v, project c world = some v → ∀ a, Reads c v a → ¬scanWrites s.machine.data coverage a) :
    Eventually (historyStep fetch) (fun t =>
      t.machine.pc = Image.Lookup.entry+0xb2 ∧
      t.machine.data.regs.rbx = s.machine.data.regs.rbx ∧
      t.machine.data.regs.rbp = s.machine.data.regs.rbp ∧
      StableTrace s.machine.data coverage preempt c.rxSection s.history raw t ∧
      observe c.rxSection t.history = .ok seen ∧
      MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection t.history) seen source ∧
      ExecutedCorrespondence.CutsAligned (R c) c.rxSection t.history source ∧
      R c t.history seen t.machine world) s := by
  have run := scan_call_cursor fetch "L_ffffffff810f31f0" s (by
      rw [pc]
      exact agree _ _ (by rfl)) .pc tracePc s.machine.data coverage preempt
    (ScanFrame.initial _ _ _ ready) ready.pc_allowed c.rxSection raw rawObserved related.1
    (by simp [pc, LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
    (by constructor <;> simp [pc, Image.Lookup.entry, Image.PeerGet.entry])
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
  rintro t ⟨nextPc, bx, bp, traced⟩
  obtain ⟨tail, recorded, cuts⟩ := traced.extension
  have full : observe c.rxSection t.history = .ok seen := by
    rw [recorded]
    simpa only [List.append_nil] using observe_extend_raw c.rxSection s.history tail seen raw []
      observed rawObserved (by simpa only [recorded, List.append_nil] using traced.observed)
  have newR := related.advance_inactive c s.history t.history seen [] s.machine t.machine world
    traced.last (by intro p member; cases member) inactive noReturn _ traced.frame.memory apart
  have newCuts := bucket_cuts c world s.machine s.history tail seen [] source related observed
    (by simpa only [List.append_nil, recorded] using full) matched aligned latest
    (by intro p member; cases member) (by intro p member; cases member) inactive noReturn
    _ (fun q member cut => (cuts q member cut).memory) apart
  refine ⟨by simpa only [pc, show Image.Lookup.entry+0xad+5 = Image.Lookup.entry+0xb2 from rfl] using nextPc,
    bx, bp, traced, full, ?_, ?_, ?_⟩
  · simpa only [recorded] using ExecutedCorrespondence.matched_append_history matched tail
  · simpa only [List.filterMap_nil, LookupSearch.decisionWorlds, List.append_nil, recorded] using newCuts
  · simpa only [List.filterMap_nil, LookupSearch.advance, List.append_nil] using newR

#print axioms R.frame_no_pending
#print axioms selected_callback
end Binary.LookupRelation
