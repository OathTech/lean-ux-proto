import ScanType
import LoopSearch

namespace Binary.LookupHistory
open TrustBase
local instance : Labels := Image.linkedLabels

def bucketSteps (rxSection query : Nat) (kinds : List Leanux.WG.IndexKind) :
    List (Address × Leanux.WG.IndexEntry) → List Leanux.Step
  | [] => [{decision := .idxWalk, outcome := false, netRx := rxSection},
      {decision := .idxFound, outcome := false, netRx := rxSection}]
  | cell :: rest =>
    {decision := .idxWalk, outcome := true, netRx := rxSection} ::
    {decision := .idxMatch, outcome := cell.2.index == query, netRx := rxSection} ::
    (if cell.2.index == query then
      [{decision := .idxTypeMatch, outcome := kinds.contains cell.2.kind, netRx := rxSection},
       {decision := .idxFound, outcome := kinds.contains cell.2.kind, netRx := rxSection}]
     else bucketSteps rxSection query kinds rest)

theorem bucketSteps_split (rxSection query : Nat) (kinds : List Leanux.WG.IndexKind)
    (es : List (Address × Leanux.WG.IndexEntry)) :
    bucketSteps rxSection query kinds es = scanSteps rxSection query es ++
      (match firstIndex query es with
       | none => []
       | some (_,e) =>
         [{decision := .idxTypeMatch, outcome := kinds.contains e.kind, netRx := rxSection},
          {decision := .idxFound, outcome := kinds.contains e.kind, netRx := rxSection}]) := by
  induction es with
  | nil => rfl
  | cons cell es ih =>
    cases hit : (cell.2.index == query) <;> simp [bucketSteps, scanSteps, firstIndex, hit, ih]

/-- Exact decisions of the actual logged source prefix, rather than an
    independent expected-output model. Addresses have no source counterpart. -/
theorem source_bucket_steps (kinds : List Leanux.WG.IndexKind) (query : Nat)
    (es : List (Address × Leanux.WG.IndexEntry)) (history : List MirrorHistory.Point) (w : Leanux.World) :
    (LookupSearch.result kinds query (es.map Prod.snd) history w).2.steps.toList =
      w.steps.toList ++ bucketSteps w.netRxSection query kinds es := by
  induction es generalizing history w with
  | nil => simp [LookupSearch.result_nil, LookupSearch.finish, LookupMirror.record, bucketSteps]
  | cons cell es ih =>
    rcases cell with ⟨a,e⟩
    simp only [List.map_cons]
    cases hit : (e.index == query) with
    | false =>
      rw [LookupSearch.result_miss kinds query e (es.map Prod.snd) history w hit, ih]
      simp [LookupMirror.record, bucketSteps, hit, List.append_assoc]
    | true =>
      rw [LookupSearch.result_hit kinds query e (es.map Prod.snd) history w hit]
      cases good : kinds.contains e.kind <;>
        simp [LookupSearch.finish, LookupMirror.record, bucketSteps, hit, good, List.append_assoc]

def bucketExitBase (base : MachineData) (query : Nat) (es : List (Address × Leanux.WG.IndexEntry)) : MachineData :=
  match firstIndex query es with
  | none => base
  | some (_,e) => kindBase base (.ofBitVec (kindWord e.kind))

def BucketStop (query : Nat) (kinds : List Leanux.WG.IndexKind)
    (es : List (Address × Leanux.WG.IndexEntry)) (s : MachineState) : Prop :=
  match firstIndex query es with
  | none => s.pc = Image.Lookup.entry+0x6c ∧ s.data.regs.rbx = 0
  | some (a,e) =>
    s.pc = (if kinds.contains e.kind then Image.Lookup.entry+0xad else Image.Lookup.entry+0x71) ∧
    s.data.regs.rbx.toBitVec = a

/-- Complete physical bucket loop, including both kind outcomes. Every
    successor is produced by Kraken execution. The two cut-frame phases
    account for the actual AND overwrite; no accepted kind mask is removed.
    Whole-World R and source World matching remain separate obligations. -/
theorem bucket_loop (fetch : Int64 → Option Decoded) (agree : AnchoredDecoderAgreement fetch)
    (tracePc : TracePcContract fetch) (traceCmp : TraceCmp4Contract fetch)
    (traceConstCmp : TraceConstCmp4Contract fetch)
    (base : MachineData) (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (query rxSection : Nat) (kinds : List Leanux.WG.IndexKind)
    (queryReg : (base.regs.get (.low .r12 .W32)).toNat = query)
    (mask : KindMask (base.regs.get (.low .r14 .W32)) kinds)
    (es : List (Address × Leanux.WG.IndexEntry))
    (comparison : es ≠ [] → coverage.CompareAllowed preempt)
    (separate : ∀ cell ∈ es, ∀ address, BucketShapeReads cell.1 address →
      ¬scanWrites base coverage address)
    (first : Bool) (s : MachineData) (frame : ScanFrame base coverage preempt s)
    (bucket : BucketShape base.dmem s.regs.rbx.toBitVec es)
    (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s, Image.Lookup.entry+(if first then 0x2f else 0x67)⟩) :
    Eventually (historyStep fetch) (fun t =>
      BucketStop query kinds es t.machine ∧
      ScanFrame (bucketExitBase base query es) coverage preempt t.machine.data ∧
      t.history.getLast? = some t.machine ∧
      (∃ delta, delta.filterMap (·.step) = bucketSteps rxSection query kinds es ∧ DecisionPoints delta ∧
        observeHistory (LookupObservation.edge rxSection) t.history = .ok (events ++ delta)) ∧
      PeerCountPhase.StableExtension history t.history ∧
      ∃ before after, t.history = history ++ before ++ after ∧
        ScanCuts base coverage preempt before ∧
        ScanCuts (bucketExitBase base query es) coverage preempt after ∧
        (match firstIndex query es with
         | none => after = []
         | some _ => ∃ boundary, (history ++ before).getLast? = some boundary ∧
             boundary.pc = Image.Lookup.entry+0x9a ∧ ScanFrame base coverage preempt boundary.data))
      ⟨⟨s, Image.Lookup.entry+(if first then 0x2f else 0x67)⟩, history⟩ := by
  have scan := scan_search fetch agree tracePc traceCmp base coverage preempt query rxSection queryReg
    es comparison separate first s frame bucket history events observed last
  apply eventually_trans (historyStep fetch) _ _ _ scan
  rintro t₁ ⟨stop, delta, records, tags, trace⟩
  cases found : firstIndex query es with
  | none =>
    apply Eventually.done
    obtain ⟨before, recorded, cuts⟩ := trace.extension
    refine ⟨?_, ?_, trace.last, ⟨delta, ?_, tags, trace.observed⟩, trace.stable, before, [], ?_, cuts, ?_, by simp only [found]⟩
    · simpa only [BucketStop, ScanStop, found] using stop
    · simpa only [bucketExitBase, found] using trace.frame
    · simpa only [bucketSteps_split, found, List.append_nil] using records
    · simpa only [List.append_nil] using recorded
    · intro q member _; cases member
  | some cell =>
    rcases cell with ⟨a,e⟩
    have canCompare := comparison (by intro empty; subst es; cases found)
    obtain ⟨rest, represented, members⟩ := firstIndex_bucket query base.dmem es _ a e bucket found
    have hit : t₁.machine.pc = Image.Lookup.entry+0x95 ∧ t₁.machine.data.regs.rbx.toBitVec = a ∧
        (t₁.machine.data.regs.get (.low .rbp .W32)).toNat = e.index := by
      simpa only [ScanStop, found] using stop
    have suffix := matched_type_exit fetch agree tracePc traceConstCmp base t₁.machine.data coverage preempt
      trace.frame a e rest hit.2.1 represented (fun cell member => separate cell (members cell member)) kinds mask
      canCompare rxSection t₁.history (events ++ delta) trace.observed (by rw [← hit.1]; exact trace.last)
    have cursor : (⟨⟨t₁.machine.data, Image.Lookup.entry+0x95⟩, t₁.history⟩ : Executed) = t₁ := by rw [← hit.1]
    rw [cursor] at suffix
    apply eventually_weaken (historyStep fetch) _ _ _ _ suffix
    rintro t₂ ⟨pc, bx, frame, observed, last, stable, before, after, recorded, beforeCuts, afterCuts, boundary, boundaryLast, boundaryPC, boundaryFrame⟩
    let typePoints := [LookupObservation.decision rxSection .idxTypeMatch (kinds.contains e.kind) t₂.machine,
      LookupObservation.decision rxSection .idxFound (kinds.contains e.kind) t₂.machine]
    obtain ⟨scanTail, scanRecorded, scanCuts⟩ := trace.extension
    refine ⟨?_, ?_, last, ⟨delta ++ typePoints, ?_, ?_, ?_⟩, trace.stable.trans stable, scanTail ++ before, after, ?_,
      ScanCuts.append scanCuts beforeCuts, ?_, ?_⟩
    · simpa only [BucketStop, found] using And.intro pc bx
    · simpa only [bucketExitBase, found] using frame
    · rw [bucketSteps_split, found]
      simp [List.filterMap_append, records, typePoints, LookupObservation.decision]
    · exact tags.append ((decision_point _ _ _ _).append (decision_point _ _ _ _))
    · simpa only [List.append_assoc] using observed
    · rw [recorded, scanRecorded]
      simp only [List.append_assoc]
    · simpa only [bucketExitBase, found] using afterCuts
    · simp only [found]
      refine ⟨boundary, ?_, boundaryPC, boundaryFrame⟩
      rw [scanRecorded, List.append_assoc] at boundaryLast
      exact boundaryLast

#print axioms bucket_loop

#print axioms bucketSteps_split
#print axioms source_bucket_steps
end Binary.LookupHistory
