import LookupHelperEntry
import FirstScanFrame
namespace Binary.LookupRelation.First
open Leanux Leanux.WG TrustBase LookupHistory LookupObservation PeerCountPhase Callback LookupHistory.First
local instance : Labels := Image.linkedLabels
variable {outer : UInt64}
/-- The selected bucket exit first executes its real PC callback. The
    helper's owner-word load starts only at the resulting +b2 cursor. -/
theorem selected_callback (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (tracePc : LeafService fetch (.ofNat 0xffffffff810f3100) (KcovReady .pc) (KcovWrites .pc) (KcovEffect .pc))
    (c : Config) (world : World) (s : Executed)
    (pc : s.machine.pc = Image.Lookup.entry+0xad)
    (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (safe : CallStackSafe outer s.machine.data.regs.rsp)
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
    Eventually (guardedHistoryStep fetch (StackGuard outer)) (fun t =>
      t.machine.pc = Image.Lookup.entry+0xb2 ∧
      t.machine.data.regs.rbx = s.machine.data.regs.rbx ∧
      t.machine.data.regs.rbp = s.machine.data.regs.rbp ∧
      StableTrace s.machine.data coverage preempt c.rxSection s.history raw t ∧
      observe c.rxSection t.history = .ok seen ∧
      MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection t.history) seen source ∧
      ExecutedCorrespondence.CutsAligned (R c) c.rxSection t.history source ∧
      R c t.history seen t.machine world) s := by
  have run := scan_call_cursor fetch "L_ffffffff810f3100" s (by
      rw [pc]
      exact agree _ _ (by rfl)) .pc tracePc s.machine.data coverage preempt
    safe (ScanFrame.initial _ _ _ ready) ready.pc_allowed c.rxSection raw rawObserved related.1
    (by simp [pc, LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
    (by constructor <;> simp [pc, Image.Lookup.entry, Image.PeerGet.entry])
  apply eventually_weaken (guardedHistoryStep fetch (StackGuard outer)) _ _ _ _ run
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
end Binary.LookupRelation.First
