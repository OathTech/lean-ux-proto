import LookupBucketSimulation
import FirstBucketScan
namespace Binary.LookupRelation.First
open Leanux Leanux.WG TrustBase LookupHistory Callback
local instance : Labels := Image.linkedLabels
variable {outer : UInt64}

theorem bucket_related (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch)
    (tracePc : LeafService fetch (.ofNat 0xffffffff810f3100) (KcovReady .pc) (KcovWrites .pc) (KcovEffect .pc)) (traceCmp : LeafService fetch (.ofNat 0xffffffff810f3e80) (KcovReady .cmp4) (KcovWrites .cmp4) (KcovEffect .cmp4))
    (traceConstCmp : LeafService fetch (.ofNat 0xffffffff810f3f00) (KcovReady .constCmp4) (KcovWrites .constCmp4) (KcovEffect .constCmp4))
    (c : Config) (world : World) (v : View) (projected : project c world = some v)
    (base : MachineData) (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (safe : LookupHistory.First.CallStackSafe outer base.regs.rsp)
    (ready : LookupCoverage.CallsReady coverage preempt base)
    (entryBucket : coverage.entryView.bucket = v.bucket)
    (currentCount : preempt = 512+coverage.entryPreempt)
    (history : List MachineState) (seen prior : List LookupObservation.Point)
    (related : R c history seen ⟨base, Image.Lookup.entry+0x2f⟩ world)
    (observed : LookupObservation.observe c.rxSection history = .ok seen)
    (rawObserved : observeHistory (LookupObservation.edge c.rxSection) history = .ok prior)
    (inactive : helperActive seen = false) (noReturn : lastHelperReturn seen = none)
    (query : (base.regs.get (.low .r12 .W32)).toNat = c.query)
    (mask : KindMask (base.regs.get (.low .r14 .W32)) c.kinds)
    (cursor : base.dmem.loadInt (c.table + .ofNat 64 (8 * (c.query % 8192))) 8 =
      some (base.regs.rbx.toBitVec.toNat : Int))
    (apart : ∀ address, Reads c v address → ¬scanWrites base coverage address)
    (sourceHistory : List MirrorHistory.Point) :
    Eventually (guardedHistoryStep fetch (StackGuard outer)) (fun t =>
      BucketStop c.query c.kinds (cells c v) t.machine ∧
      ScanFrame (bucketExitBase base c.query (cells c v)) coverage preempt t.machine.data ∧
      t.history.getLast? = some t.machine ∧
      ∃ delta,
        delta.filterMap (·.step) = bucketSteps c.rxSection c.query c.kinds (cells c v) ∧
        DecisionPoints delta ∧
        (∀ point ∈ delta, point.machine.pc ∈ Image.cutPoints) ∧
        LookupObservation.observe c.rxSection t.history = .ok (seen ++ delta) ∧
        observeHistory (LookupObservation.edge c.rxSection) t.history = .ok (prior ++ delta) ∧
        R c t.history (seen ++ delta) t.machine
          (LookupSearch.result c.kinds c.query v.bucket sourceHistory world).2 ∧
        PeerCountPhase.StableExtension history t.history ∧
        ∃ tail, t.history = history ++ tail ∧
          ∀ state ∈ tail, state.pc ∈ Image.cutPoints →
            EqualOutside (scanWrites base coverage) base.dmem state.data.dmem)
      ⟨⟨base, Image.Lookup.entry+0x2f⟩, history⟩ := by
  have physical : Physical c history seen ⟨base, Image.Lookup.entry+0x2f⟩ v := by
    obtain ⟨other, otherProjection, physical⟩ := related.2.1
    have same : other = v := Option.some.inj (otherProjection.symm.trans projected)
    simpa only [same] using physical
  obtain ⟨head, loaded, bucket⟩ := physical.2.1
  have headEq : head = base.regs.rbx.toBitVec := by
    apply BitVec.eq_of_toNat_eq
    have equal := Option.some.inj (loaded.symm.trans cursor)
    omega
  rw [headEq] at bucket
  have separate : ∀ cell ∈ cells c v, ∀ address, BucketShapeReads cell.1 address →
      ¬scanWrites base coverage address := by
    intro cell member address read
    obtain ⟨entry, present, equal⟩ := List.mem_map.mp member
    subst cell
    exact apart address (.inr (.inl ⟨entry, present, read⟩))
  have comparison : cells c v ≠ [] → coverage.CompareAllowed preempt := by
    intro nonempty
    refine ⟨currentCount, ?_⟩
    intro empty
    rw [entryBucket] at empty
    exact nonempty (by simp [cells, empty])
  have run := LookupHistory.First.bucket_loop fetch agree tracePc traceCmp traceConstCmp base coverage preempt
    c.query c.rxSection c.kinds query mask safe (cells c v) comparison separate true base
    (ScanFrame.initial base coverage preempt ready) bucket history prior rawObserved related.1
  apply eventually_weaken (guardedHistoryStep fetch (StackGuard outer)) _ _ _ _ run
  rintro t ⟨stop, frame, last, ⟨delta, records, tags, rawFull⟩,
    stable, before, after, recorded, firstCuts, secondCuts, _⟩
  have extended : t.history = history ++ (before ++ after) := by
    simpa only [List.append_assoc] using recorded
  have full := LookupObservation.observe_extend_raw c.rxSection history (before ++ after)
    seen prior delta observed rawObserved (by simpa only [← extended] using rawFull)
  have memory : EqualOutside (scanWrites base coverage) base.dmem t.machine.data.dmem := by
    simpa only [bucketExitBase_writes, bucketExitBase_memory] using frame.memory
  have finalR := related.advance_inactive c history t.history seen delta
    ⟨base, Image.Lookup.entry+0x2f⟩ t.machine world last tags inactive noReturn
    (scanWrites base coverage) memory (by
      intro other otherProjection address read
      have same : other = v := Option.some.inj (otherProjection.symm.trans projected)
      subst other
      exact apart address read)
  have mapped : (cells c v).map Prod.snd = v.bucket := by simp [cells, List.map_map, Function.comp_def]
  have sourceFinal := (LookupSearch.result_worlds c.kinds c.query (cells c v) sourceHistory world).2
  rw [mapped, related.2.2.2] at sourceFinal
  refine ⟨stop, frame, last, delta, records, tags, ?_, ?_, rawFull, ?_, stable, before ++ after, extended, ?_⟩
  · exact bucket_delta_cuts c.rxSection c.query c.kinds (cells c v) t.history prior delta records tags rawFull
  · simpa only [← extended] using full
  · rw [sourceFinal]
    simpa only [records] using finalR
  · exact bucketCuts_memory base coverage preempt c.query (cells c v)
      before after firstCuts secondCuts

/-- Match every newly emitted decision to its exact source World and raw
    instruction prefix. The physical frame is used only at the actual
    emitting occurrence inside the executed suffix. -/theorem bucket_simulation (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch)
    (tracePc : LeafService fetch (.ofNat 0xffffffff810f3100) (KcovReady .pc) (KcovWrites .pc) (KcovEffect .pc)) (traceCmp : LeafService fetch (.ofNat 0xffffffff810f3e80) (KcovReady .cmp4) (KcovWrites .cmp4) (KcovEffect .cmp4))
    (traceConstCmp : LeafService fetch (.ofNat 0xffffffff810f3f00) (KcovReady .constCmp4) (KcovWrites .constCmp4) (KcovEffect .constCmp4))
    (c : Config) (world : World) (v : View) (projected : project c world = some v)
    (base : MachineData) (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (safe : LookupHistory.First.CallStackSafe outer base.regs.rsp)
    (ready : LookupCoverage.CallsReady coverage preempt base)
    (entryBucket : coverage.entryView.bucket = v.bucket)
    (currentCount : preempt = 512+coverage.entryPreempt)
    (history : List MachineState) (seen prior : List LookupObservation.Point)
    (related : R c history seen ⟨base, Image.Lookup.entry+0x2f⟩ world)
    (observed : LookupObservation.observe c.rxSection history = .ok seen)
    (rawObserved : observeHistory (LookupObservation.edge c.rxSection) history = .ok prior)
    (inactive : helperActive seen = false) (noReturn : lastHelperReturn seen = none)
    (query : (base.regs.get (.low .r12 .W32)).toNat = c.query)
    (mask : KindMask (base.regs.get (.low .r14 .W32)) c.kinds)
    (cursor : base.dmem.loadInt (c.table + .ofNat 64 (8 * (c.query % 8192))) 8 =
      some (base.regs.rbx.toBitVec.toNat : Int))
    (apart : ∀ address, Reads c v address → ¬scanWrites base coverage address)
    (sourceHistory : List MirrorHistory.Point)
    (matched : LookupObservation.MatchesPoints
      (ExecutedCorrespondence.AtPoint (R c) c.rxSection history) seen sourceHistory)
    (aligned : ExecutedCorrespondence.CutsAligned (R c) c.rxSection history sourceHistory)
    (latest : sourceHistory.getLast?.map (·.world) = some world) :
    Eventually (guardedHistoryStep fetch (StackGuard outer)) (fun t =>
      BucketStop c.query c.kinds (cells c v) t.machine ∧
      ScanFrame (bucketExitBase base c.query (cells c v)) coverage preempt t.machine.data ∧
      ∃ delta,
        LookupObservation.observe c.rxSection t.history = .ok (seen ++ delta) ∧
        observeHistory (LookupObservation.edge c.rxSection) t.history = .ok (prior ++ delta) ∧
        LookupObservation.MatchesPoints
          (ExecutedCorrespondence.AtPoint (R c) c.rxSection t.history) (seen ++ delta)
          (LookupSearch.result c.kinds c.query v.bucket sourceHistory world).1.2 ∧
        ExecutedCorrespondence.CutsAligned (R c) c.rxSection t.history
          (LookupSearch.result c.kinds c.query v.bucket sourceHistory world).1.2 ∧
        R c t.history (seen ++ delta) t.machine
          (LookupSearch.result c.kinds c.query v.bucket sourceHistory world).2 ∧
        PeerCountPhase.StableExtension history t.history ∧ DecisionPoints delta ∧
        ∃ tail, t.history = history ++ tail ∧
          ∀ q ∈ tail, q.pc ∈ Image.cutPoints →
            EqualOutside (scanWrites base coverage) base.dmem q.data.dmem)
      ⟨⟨base, Image.Lookup.entry+0x2f⟩, history⟩ := by
  have run := bucket_related fetch agree tracePc traceCmp traceConstCmp c world v projected
    base coverage preempt safe ready entryBucket currentCount history seen prior related observed rawObserved inactive
    noReturn query mask cursor apart sourceHistory
  apply eventually_weaken (guardedHistoryStep fetch (StackGuard outer)) _ _ _ _ run
  rintro t ⟨stop, frame, last, delta, records, tags, cuts, observedFull, rawFull, finalR, stable, tail, recorded, frames⟩
  have separate : ∀ view, project c world = some view →
      ∀ address, Reads c view address → ¬scanWrites base coverage address := by
    intro view projection address read
    have equal : view = v := Option.some.inj (projection.symm.trans projected)
    subst view
    exact apart address read
  have observedTail : LookupObservation.observe c.rxSection (history ++ tail) = .ok (seen ++ delta) := by
    simpa only [← recorded] using observedFull
  have newPoints := bucket_points c world ⟨base, Image.Lookup.entry+0x2f⟩ history tail
    seen delta related observed observedTail tags cuts inactive noReturn
    (scanWrites base coverage) frames separate
  have oldPoints := ExecutedCorrespondence.matched_append_history matched tail
  have allPoints := oldPoints.append newPoints
  have allCuts := bucket_cuts c world ⟨base, Image.Lookup.entry+0x2f⟩ history tail
    seen delta sourceHistory related observed observedTail matched aligned latest tags cuts
    inactive noReturn (scanWrites base coverage) frames separate
  have sourcePoints := (LookupSearch.result_worlds c.kinds c.query (cells c v) sourceHistory world).1
  have mapped : (cells c v).map Prod.snd = v.bucket := by
    simp [cells, List.map_map, Function.comp_def]
  rw [mapped, related.2.2.2, ← records] at sourcePoints
  refine ⟨stop, frame, delta, observedFull, rawFull, ?_, ?_, finalR, stable, tags, tail, recorded, frames⟩
  · simpa only [recorded, sourcePoints] using allPoints
  · simpa only [recorded, sourcePoints] using allCuts
#print axioms bucket_related
#print axioms bucket_simulation
end Binary.LookupRelation.First
