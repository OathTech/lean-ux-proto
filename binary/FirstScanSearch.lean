import ScanSearch
import FirstScanIteration
namespace Binary.LookupHistory.First
open TrustBase Callback
local instance : Labels := Image.linkedLabels
variable {outer : UInt64}

theorem scan_search (fetch : Int64 → Option Decoded) (agree : AnchoredDecoderAgreement fetch)
    (tracePc : LeafService fetch (.ofNat 0xffffffff810f3100) (KcovReady .pc) (KcovWrites .pc) (KcovEffect .pc)) (traceCmp : LeafService fetch (.ofNat 0xffffffff810f3e80) (KcovReady .cmp4) (KcovWrites .cmp4) (KcovEffect .cmp4))
    (base : MachineData) (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (query rxSection : Nat)
    (queryReg : (base.regs.get (.low .r12 .W32)).toNat = query)
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
      ScanStop query es t.machine ∧ ∃ delta,
      delta.filterMap (·.step) = scanSteps rxSection query es ∧ DecisionPoints delta ∧
      StableTrace base coverage preempt rxSection history (events ++ delta) t)
      ⟨⟨s, Image.Lookup.entry+(if first then 0x2f else 0x67)⟩, history⟩ := by
  induction es generalizing s first history events with
  | nil =>
    have zero : s.regs.rbx.toBitVec = 0 := bucket
    have regZero : s.regs.rbx = 0 := UInt64.toBitVec_inj.mp zero
    have walk := scan_walk fetch agree first base s coverage preempt safe frame rxSection history events observed last
    apply eventually_weaken (guardedHistoryStep fetch (StackGuard outer)) _ _ _ _ walk
    rintro t ⟨af, machine, trace⟩
    have testedZero : s.regs.get (.low .rbx .W64) = 0#64 := by
      simp [Reg64s.get, Reg64s.get64, regZero, Reg.base, Reg.offset, BitVec.drop, BitVec.take]
    refine ⟨?_, walkPoints rxSection s af, ?_, walk_decision_points rxSection s af, trace⟩
    · simp only [ScanStop, firstIndex, machine, walkExit, testedZero]
      exact ⟨rfl, regZero⟩
    · simp [walkPoints, testedZero, LookupObservation.decision, scanSteps]
  | cons cell es ih =>
    rcases cell with ⟨a,e⟩
    have canCompare := comparison (by simp)
    have fields := bucket_cons_fields bucket
    have node : s.regs.rbx.toBitVec = a+8 := fields.2.1
    have nonzero : s.regs.get (.low .rbx .W64) ≠ 0#64 := by
      simpa [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop, BitVec.take]
        using bucket_cons_nonnull _ _ _ _ _ bucket
    have walk := scan_walk fetch agree first base s coverage preempt safe frame rxSection history events observed last
    apply eventually_trans (guardedHistoryStep fetch (StackGuard outer)) _ _ _ walk
    rintro t₁ ⟨af, machine₁, trace₁⟩
    have pc₁ : t₁.machine.pc = Image.Lookup.entry+0x34 := by
      simp [machine₁, walkExit, nonzero]
    have node₁ : t₁.machine.data.regs.rbx.toBitVec = a+8 := by
      rw [machine₁]; exact node
    have nodeRun := node_to_compare fetch agree tracePc traceCmp base t₁.machine.data coverage preempt
      safe trace₁.frame a e es node₁ (by rw [← node]; exact bucket) separate canCompare rxSection t₁.history
      (events ++ walkPoints rxSection s af) trace₁.observed (by rw [← pc₁]; exact trace₁.last)
    have cursor₁ : (⟨⟨t₁.machine.data, Image.Lookup.entry+0x34⟩, t₁.history⟩ : Executed) = t₁ := by rw [← pc₁]
    rw [cursor₁] at nodeRun
    apply eventually_trans (guardedHistoryStep fetch (StackGuard outer)) _ _ _ nodeRun
    rintro t₂ ⟨pc₂, bx₂, index₂, _, trace₂⟩
    have query₂ : (t₂.machine.data.regs.get (.low .r12 .W32)).toNat = query := by
      simpa only [Reg64s.get, Reg.base, Reg64s.get64, trace₂.frame.query] using queryReg
    have matchIndex : indexHit t₂.machine.data = (e.index == query) := by
      simp only [indexHit, index₂, query₂]
    have cmp := scan_compare fetch agree base t₂.machine.data coverage preempt safe trace₂.frame rxSection t₂.history
        (events ++ walkPoints rxSection s af) trace₂.observed (by rw [← pc₂]; exact trace₂.last)
    have cursor₂ : (⟨⟨t₂.machine.data, Image.Lookup.entry+0x59⟩, t₂.history⟩ : Executed) = t₂ := by rw [← pc₂]
    rw [cursor₂] at cmp
    apply eventually_trans (guardedHistoryStep fetch (StackGuard outer)) _ _ _ cmp
    rintro t₃ ⟨machine₃, trace₃⟩
    let cmpEvent := LookupObservation.decision rxSection .idxMatch (indexHit t₂.machine.data) (compareExit t₂.machine.data)
    have frontTrace := trace₁.trans (trace₂.trans trace₃)
    have walkTrue : walkPoints rxSection s af =
        [LookupObservation.decision rxSection .idxWalk true (walkExit s af)] := by
      simp [walkPoints, nonzero]
    cases hit : (e.index == query) with
    | true =>
      apply Eventually.done
      refine ⟨?_, walkPoints rxSection s af ++ [cmpEvent], ?_,
        (walk_decision_points rxSection s af).append (decision_point _ _ _ _), ?_⟩
      · simp only [ScanStop, firstIndex, hit, ite_true, machine₃, compareExit, matchIndex]
        exact ⟨True.intro, bx₂, index₂⟩
      · simp [scanSteps, hit, walkTrue, cmpEvent, matchIndex, LookupObservation.decision]
      · simpa only [List.append_assoc] using frontTrace
    | false =>
      have pc₃ : t₃.machine.pc = Image.Lookup.entry+0x5e := by
        simp [machine₃, compareExit, matchIndex, hit]
      have bx₃ : t₃.machine.data.regs.rbx.toBitVec = a := by rw [machine₃]; exact bx₂
      have miss := scan_miss fetch agree tracePc base t₃.machine.data coverage preempt safe trace₃.frame
        a e es bx₃ (by rw [← node]; exact bucket) separate rxSection t₃.history
        ((events ++ walkPoints rxSection s af) ++ [cmpEvent]) trace₃.observed
        (by rw [← pc₃]; exact trace₃.last)
      have cursor₃ : (⟨⟨t₃.machine.data, Image.Lookup.entry+0x5e⟩, t₃.history⟩ : Executed) = t₃ := by rw [← pc₃]
      rw [cursor₃] at miss
      have suffix : GuardedSegment fetch (StackGuard outer) (StableTrace base coverage preempt rxSection) t₃
          (fun seen t => ScanStop query es t.machine ∧ ∃ delta,
            seen = ((events ++ walkPoints rxSection s af) ++ [cmpEvent]) ++ delta ∧
            delta.filterMap (·.step) = scanSteps rxSection query es ∧ DecisionPoints delta) := by
        apply GuardedSegment.bind (fun first second => first.trans second) miss
        rintro t₄ seen ⟨same, next, pc₄, bx₄, baseTail, _⟩ trace₄
        subst seen
        have recur := ih (fun _ => canCompare) (fun cell member => separate cell (List.mem_cons_of_mem _ member)) false
          t₄.machine.data trace₄.frame (by rw [bx₄]; exact baseTail) t₄.history
          (((events ++ walkPoints rxSection s af) ++ [cmpEvent])) trace₄.observed
          (by change t₄.history.getLast? = some ⟨t₄.machine.data, Image.Lookup.entry+0x67⟩; rw [← pc₄]; exact trace₄.last)
        have cursor₄ : (⟨⟨t₄.machine.data, Image.Lookup.entry+0x67⟩, t₄.history⟩ : Executed) = t₄ := by rw [← pc₄]
        simp only [Bool.false_eq_true, ite_false] at recur
        rw [cursor₄] at recur
        apply eventually_weaken (guardedHistoryStep fetch (StackGuard outer)) _ _ _ _ recur
        rintro t₅ ⟨stop, delta, decisions, tags, trace₅⟩
        exact ⟨_, ⟨stop, delta, rfl, decisions, tags⟩, trace₅⟩
      apply eventually_weaken (guardedHistoryStep fetch (StackGuard outer)) _ _ _ _ suffix
      rintro t₅ ⟨seen, ⟨stop, delta, same, decisions, tags⟩, trace⟩
      subst seen
      refine ⟨?_, walkPoints rxSection s af ++ [cmpEvent] ++ delta, ?_,
        ((walk_decision_points rxSection s af).append (decision_point _ _ _ _)).append tags, ?_⟩
      · simpa only [ScanStop, firstIndex, hit, Bool.false_eq_true, ite_false] using stop
      · simp [scanSteps, hit, walkTrue, cmpEvent, matchIndex, LookupObservation.decision, decisions]
      · simpa only [List.append_assoc] using frontTrace.trans trace

#print axioms scan_search
end Binary.LookupHistory.First
