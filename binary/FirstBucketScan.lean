import BucketScan
import FirstScanType
namespace Binary.LookupHistory.First
open TrustBase Callback
local instance : Labels := Image.linkedLabels
variable {outer : UInt64}

/-- Complete physical bucket loop, including both kind outcomes. Every
    successor is produced by Kraken execution. The two cut-frame phases
    account for the actual AND overwrite; no accepted kind mask is removed.
    Whole-World R and source World matching remain separate obligations. -/
theorem bucket_loop (fetch : Int64 → Option Decoded) (agree : AnchoredDecoderAgreement fetch)
    (tracePc : LeafService fetch (.ofNat 0xffffffff810f3100) (KcovReady .pc) (KcovWrites .pc) (KcovEffect .pc)) (traceCmp : LeafService fetch (.ofNat 0xffffffff810f3e80) (KcovReady .cmp4) (KcovWrites .cmp4) (KcovEffect .cmp4))
    (traceConstCmp : LeafService fetch (.ofNat 0xffffffff810f3f00) (KcovReady .constCmp4) (KcovWrites .constCmp4) (KcovEffect .constCmp4))
    (base : MachineData) (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (query rxSection : Nat) (kinds : List Leanux.WG.IndexKind)
    (queryReg : (base.regs.get (.low .r12 .W32)).toNat = query)
    (mask : KindMask (base.regs.get (.low .r14 .W32)) kinds)
    (safe : CallStackSafe outer base.regs.rsp)
    (es : List (Address × Leanux.WG.IndexEntry))
    (comparison : es ≠ [] → coverage.CompareAllowed preempt)
    (separate : ∀ cell ∈ es, ∀ address, BucketShapeReads cell.1 address →
      ¬scanWrites base coverage address)
    (first : Bool) (s : MachineData) (frame : ScanFrame base coverage preempt s)
    (bucket : BucketShape base.dmem s.regs.rbx.toBitVec es)
    (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s, Image.Lookup.entry+(if first then 0x2f else 0x67)⟩) :
    Eventually (guardedHistoryStep fetch (StackGuard outer)) (fun t =>
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
    safe es comparison separate first s frame bucket history events observed last
  apply eventually_trans (guardedHistoryStep fetch (StackGuard outer)) _ _ _ scan
  rintro t₁ ⟨stop, delta, records, tags, trace⟩
  cases found : firstIndex query es with
  | none =>
    apply Eventually.done
    obtain ⟨before, recorded, cuts⟩ := trace.extension
    refine ⟨?_, ?_, trace.last, ⟨delta, ?_, tags, trace.observed⟩, trace.stable, before, [], ?_, cuts, ?_, by simp only⟩
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
      safe trace.frame a e rest hit.2.1 represented (fun cell member => separate cell (members cell member)) kinds mask
      canCompare rxSection t₁.history (events ++ delta) trace.observed (by rw [← hit.1]; exact trace.last)
    have cursor : (⟨⟨t₁.machine.data, Image.Lookup.entry+0x95⟩, t₁.history⟩ : Executed) = t₁ := by rw [← hit.1]
    rw [cursor] at suffix
    apply eventually_weaken (guardedHistoryStep fetch (StackGuard outer)) _ _ _ _ suffix
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
    · simp only
      refine ⟨boundary, ?_, boundaryPC, boundaryFrame⟩
      rw [scanRecorded, List.append_assoc] at boundaryLast
      exact boundaryLast

#print axioms bucket_loop

#print axioms bucketSteps_split
#print axioms source_bucket_steps
end Binary.LookupHistory.First
