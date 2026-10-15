import LookupRelation
import ObservationLocations

namespace Binary.LookupRelation
open Leanux Leanux.WG TrustBase LookupHistory
local instance : Labels := Image.linkedLabels

def cells (c : Config) (v : View) : List (Address × IndexEntry) :=
  v.bucket.map fun e => (ownerAddress c e.owner, e)

theorem bucket_steps_tags (rx query : Nat) (kinds : List IndexKind)
    (entries : List (Address × IndexEntry)) :
    ∀ step ∈ bucketSteps rx query kinds entries,
      LookupObservation.BucketTag (.decision step.decision) := by
  induction entries with
  | nil => simp [bucketSteps, LookupObservation.BucketTag]
  | cons cell rest ih =>
    cases hit : (cell.2.index == query) <;>
      simp [bucketSteps, hit, LookupObservation.BucketTag] at ih ⊢ <;> exact ih

theorem bucket_delta_cuts (rx query : Nat) (kinds : List IndexKind)
    (entries : List (Address × IndexEntry))
    (history : List MachineState) (prior delta : List LookupObservation.Point)
    (records : delta.filterMap (·.step) = bucketSteps rx query kinds entries)
    (tags : DecisionPoints delta)
    (observed : observeHistory (LookupObservation.edge rx) history = .ok (prior ++ delta)) :
    ∀ point ∈ delta, point.machine.pc ∈ Image.cutPoints := by
  intro point member
  obtain ⟨step, record, tag⟩ := tags point member
  have stepMember : step ∈ bucketSteps rx query kinds entries := by
    rw [← records]
    exact List.mem_filterMap.mpr ⟨point, member, record⟩
  apply LookupObservation.observed_bucket_cuts rx history (prior ++ delta)
    observed point (List.mem_append.mpr (.inr member))
  rw [tag]
  exact bucket_steps_tags rx query kinds entries step stepMember

/-- The physical bucket theorem composed with the lookup WG projection and
    the actual logged source computation. No owner/count effect is assumed:
    their preservation follows from the executed loop's write footprint.
    The endpoint is the first rejected/matched index or bucket exhaustion;
    per-point correspondence is established separately below. -/
theorem bucket_related (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch)
    (tracePc : TracePcContract fetch) (traceCmp : TraceCmp4Contract fetch)
    (traceConstCmp : TraceConstCmp4Contract fetch)
    (c : Config) (world : World) (v : View) (projected : project c world = some v)
    (base : MachineData) (coverage : LookupCoverage.Context) (preempt : BitVec 32)
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
    Eventually (historyStep fetch) (fun t =>
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
  have run := bucket_loop fetch agree tracePc traceCmp traceConstCmp base coverage preempt
    c.query c.rxSection c.kinds query mask (cells c v) comparison separate true base
    (ScanFrame.initial base coverage preempt ready) bucket history prior rawObserved related.1
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
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
    emitting occurrence inside the executed suffix. -/
theorem bucket_points (c : Config) (world : World) (s : MachineState)
    (history tail : List MachineState) (seen delta : List LookupObservation.Point)
    (related : R c history seen s world)
    (observed : LookupObservation.observe c.rxSection history = .ok seen)
    (full : LookupObservation.observe c.rxSection (history ++ tail) = .ok (seen ++ delta))
    (tags : DecisionPoints delta)
    (cuts : ∀ point ∈ delta, point.machine.pc ∈ Image.cutPoints)
    (inactive : helperActive seen = false) (noReturn : lastHelperReturn seen = none)
    (writes : Address → Prop)
    (frames : ∀ state ∈ tail, state.pc ∈ Image.cutPoints →
      EqualOutside writes s.data.dmem state.data.dmem)
    (apart : ∀ v, project c world = some v → ∀ address, Reads c v address → ¬writes address) :
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
  have pointR := related.advance_inactive c history ((history ++ tail).take (i + 1))
    seen (before ++ [point]) s point.machine world last partialTags inactive noReturn
    writes (frames point.machine inTail (cuts point pointMember)) apart
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

/-- Every appended stuttering cut uses the latest World in the same fixed
    source run. Rebuild matching on its actual raw prefix, rather than
    choosing an arbitrary earlier occurrence from the completed history. -/
theorem bucket_cuts (c : Config) (world : World) (s : MachineState)
    (history tail : List MachineState) (seen delta : List LookupObservation.Point)
    (sourceHistory : List MirrorHistory.Point)
    (related : R c history seen s world)
    (observed : LookupObservation.observe c.rxSection history = .ok seen)
    (full : LookupObservation.observe c.rxSection (history ++ tail) = .ok (seen ++ delta))
    (matched : LookupObservation.MatchesPoints
      (ExecutedCorrespondence.AtPoint (R c) c.rxSection history) seen sourceHistory)
    (aligned : ExecutedCorrespondence.CutsAligned (R c) c.rxSection history sourceHistory)
    (latest : sourceHistory.getLast?.map (·.world) = some world)
    (tags : DecisionPoints delta)
    (cuts : ∀ point ∈ delta, point.machine.pc ∈ Image.cutPoints)
    (inactive : helperActive seen = false) (noReturn : lastHelperReturn seen = none)
    (writes : Address → Prop)
    (frames : ∀ state ∈ tail, state.pc ∈ Image.cutPoints →
      EqualOutside writes s.data.dmem state.data.dmem)
    (apart : ∀ v, project c world = some v → ∀ address, Reads c v address → ¬writes address) :
    ExecutedCorrespondence.CutsAligned (R c) c.rxSection (history ++ tail)
      (sourceHistory ++ LookupSearch.decisionWorlds world (delta.filterMap (·.step))) := by
  intro i current present cut
  by_cases old : i < history.length
  · have oldPresent : history[i]? = some current := by
      simpa only [List.getElem?_append_left old] using present
    have oldCut := (aligned.append_source
      (LookupSearch.decisionWorlds world (delta.filterMap (·.step)))) i current oldPresent cut
    simpa only [List.take_append_of_le_length (by omega : i + 1 ≤ history.length)] using oldCut
  · have later : history.length ≤ i := by omega
    let n := i + 1 - history.length
    let middle := tail.take n
    let rest := tail.drop n
    have restored : history ++ middle ++ rest = history ++ tail := by
      simp only [middle, rest, List.append_assoc, List.take_append_drop]
    have rawPrefix : (history ++ tail).take (i + 1) = history ++ middle := by
      rw [List.take_append, List.take_of_length_le (by omega)]
    obtain ⟨localDelta, remaining, deltaEq, localObs⟩ :=
      LookupObservation.observe_between c.rxSection history middle rest seen delta
        observed (by simpa only [restored] using full)
    have localMember : ∀ p ∈ localDelta, p ∈ delta := by
      intro p member
      rw [deltaEq]
      exact List.mem_append.mpr (.inl member)
    have localTags : DecisionPoints localDelta := fun p member => tags p (localMember p member)
    have localCuts : ∀ p ∈ localDelta, p.machine.pc ∈ Image.cutPoints :=
      fun p member => cuts p (localMember p member)
    have localFrames : ∀ state ∈ middle, state.pc ∈ Image.cutPoints →
        EqualOutside writes s.data.dmem state.data.dmem := by
      intro state member isCut
      exact frames state (List.mem_of_mem_take member) isCut
    have newPoints := bucket_points c world s history middle seen localDelta related
      observed localObs localTags localCuts inactive noReturn writes localFrames apart
    have oldPoints := ExecutedCorrespondence.matched_append_history matched middle
    have allPoints := oldPoints.append newPoints
    let sourcePart := sourceHistory ++
      LookupSearch.decisionWorlds world (localDelta.filterMap (·.step))
    let sourceRest := LookupSearch.decisionWorlds
      (LookupSearch.advance world (localDelta.filterMap (·.step)))
      (remaining.filterMap (·.step))
    have sourceEq : sourceHistory ++ LookupSearch.decisionWorlds world (delta.filterMap (·.step)) =
        sourcePart ++ sourceRest := by
      rw [deltaEq, List.filterMap_append, LookupSearch.decisionWorlds_append]
      simp only [sourcePart, sourceRest, List.append_assoc]
    have lengthEq : (seen ++ localDelta).length = sourcePart.length := allPoints.length_eq
    have takeEq : (sourceHistory ++ LookupSearch.decisionWorlds world (delta.filterMap (·.step))).take
        (seen ++ localDelta).length = sourcePart := by
      rw [sourceEq, lengthEq, List.take_left]
    have prefixMatched : LookupObservation.PrefixMatches
        (ExecutedCorrespondence.AtPoint (R c) c.rxSection (history ++ middle))
        (seen ++ localDelta)
        (sourceHistory ++ LookupSearch.decisionWorlds world (delta.filterMap (·.step))) := by
      refine ⟨?_, ?_⟩
      · rw [sourceEq, lengthEq]
        simpa only [List.length_append] using Nat.le_add_right sourcePart.length sourceRest.length
      · simpa only [takeEq] using allPoints
    have currentInTail : current ∈ tail := by
      have found : tail[i - history.length]? = some current := by
        simpa only [List.getElem?_append_right later] using present
      exact List.mem_of_getElem? found
    have last : (history ++ middle).getLast? = some current := by
      rw [← rawPrefix, List.getLast?_take]
      simp [present]
    have currentR := related.advance_inactive c history (history ++ middle)
      seen localDelta s current world last localTags inactive noReturn writes
      (frames current currentInTail cut) apart
    have latestWorld := LookupSearch.latest_world sourceHistory world latest
      (localDelta.filterMap (·.step))
    change sourcePart.getLast?.map (·.world) = _ at latestWorld
    cases lastPoint : sourcePart.getLast? with
    | none => rw [lastPoint] at latestWorld; cases latestWorld
    | some point =>
      rw [lastPoint] at latestWorld
      have worldEq : point.world = LookupSearch.advance world (localDelta.filterMap (·.step)) :=
        Option.some.inj latestWorld
      refine ⟨seen ++ localDelta, point, ?_, ?_, ?_, ?_⟩
      · simpa only [rawPrefix] using localObs
      · simpa only [rawPrefix] using prefixMatched
      · simpa only [takeEq] using lastPoint
      · simpa only [rawPrefix, worldEq] using currentR

/-- The entire bucket segment, with its concrete WG relation at every
    decision, call/comparison cut and endpoint, composed from Kraken execution. -/
theorem bucket_simulation (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch)
    (tracePc : TracePcContract fetch) (traceCmp : TraceCmp4Contract fetch)
    (traceConstCmp : TraceConstCmp4Contract fetch)
    (c : Config) (world : World) (v : View) (projected : project c world = some v)
    (base : MachineData) (coverage : LookupCoverage.Context) (preempt : BitVec 32)
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
    Eventually (historyStep fetch) (fun t =>
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
        PeerCountPhase.StableExtension history t.history)
      ⟨⟨base, Image.Lookup.entry+0x2f⟩, history⟩ := by
  have run := bucket_related fetch agree tracePc traceCmp traceConstCmp c world v projected
    base coverage preempt ready entryBucket currentCount history seen prior related observed rawObserved inactive
    noReturn query mask cursor apart sourceHistory
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
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
  refine ⟨stop, frame, delta, observedFull, rawFull, ?_, ?_, finalR, stable⟩
  · simpa only [recorded, sourcePoints] using allPoints
  · simpa only [recorded, sourcePoints] using allCuts

#print axioms bucket_simulation

#print axioms bucket_cuts
#print axioms bucket_points
#print axioms bucket_steps_tags
#print axioms bucket_delta_cuts
#print axioms bucket_related
end Binary.LookupRelation
