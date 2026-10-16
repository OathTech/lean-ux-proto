import ScanIteration

namespace Binary.LookupHistory
open TrustBase
local instance : Labels := Image.linkedLabels

/-- Physical scan stopping before the matched kind test. A matching index
    terminates even if a later kind test will reject that entry. -/
def firstIndex (query : Nat) : List (Address × Leanux.WG.IndexEntry) → Option (Address × Leanux.WG.IndexEntry)
  | [] => none
  | cell :: rest => if cell.2.index == query then some cell else firstIndex query rest

def scanSteps (rxSection query : Nat) : List (Address × Leanux.WG.IndexEntry) → List Leanux.Step
  | [] => [{decision := .idxWalk, outcome := false, netRx := rxSection},
      {decision := .idxFound, outcome := false, netRx := rxSection}]
  | cell :: rest =>
    {decision := .idxWalk, outcome := true, netRx := rxSection} ::
    {decision := .idxMatch, outcome := cell.2.index == query, netRx := rxSection} ::
    (if cell.2.index == query then [] else scanSteps rxSection query rest)

def ScanStop (query : Nat) (es : List (Address × Leanux.WG.IndexEntry)) (s : MachineState) : Prop :=
  match firstIndex query es with
  | none => s.pc = Image.Lookup.entry+0x6c ∧ s.data.regs.rbx = 0
  | some (a,e) => s.pc = Image.Lookup.entry+0x95 ∧ s.data.regs.rbx.toBitVec = a ∧
      (s.data.regs.get (.low .rbp .W32)).toNat = e.index

/-- A scan emits only decision points. Keeping this beside the filtered
    records excludes hidden call/return points with step=none. -/
def DecisionPoints (points : List LookupObservation.Point) : Prop :=
  ∀ p ∈ points, ∃ step, p.step = some step ∧ p.tag = .decision step.decision

theorem DecisionPoints.append {first second : List LookupObservation.Point}
    (a : DecisionPoints first) (b : DecisionPoints second) : DecisionPoints (first ++ second) := by
  intro p member
  rcases List.mem_append.mp member with h | h
  · exact a p h
  · exact b p h

theorem decision_point (rxSection : Nat) (d : Leanux.Decision) (b : Bool) (s : MachineState) :
    DecisionPoints [LookupObservation.decision rxSection d b s] := by
  intro p member
  have eq := List.mem_singleton.mp member
  subst p
  exact ⟨_, rfl, rfl⟩

theorem walk_decision_points (rxSection : Nat) (s : MachineData) (af : Bool) :
    DecisionPoints (walkPoints rxSection s af) := by
  cases h : decide (s.regs.get (.low .rbx .W64) ≠ 0) with
  | true => simpa only [walkPoints, h, ite_true, List.append_nil] using
      decision_point rxSection .idxWalk true (walkExit s af)
  | false =>
    simpa only [walkPoints, h, Bool.false_eq_true, ite_false] using
      ((decision_point rxSection .idxWalk false (walkExit s af)).append
        (decision_point rxSection .idxFound false (walkExit s af)))

theorem scan_search (fetch : Int64 → Option Decoded) (agree : AnchoredDecoderAgreement fetch)
    (tracePc : TracePcContract fetch) (traceCmp : TraceCmp4Contract fetch)
    (base : MachineData) (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (query rxSection : Nat)
    (queryReg : (base.regs.get (.low .r12 .W32)).toNat = query)
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
      ScanStop query es t.machine ∧ ∃ delta,
      delta.filterMap (·.step) = scanSteps rxSection query es ∧ DecisionPoints delta ∧
      StableTrace base coverage preempt rxSection history (events ++ delta) t)
      ⟨⟨s, Image.Lookup.entry+(if first then 0x2f else 0x67)⟩, history⟩ := by
  induction es generalizing s first history events with
  | nil =>
    have zero : s.regs.rbx.toBitVec = 0 := bucket
    have regZero : s.regs.rbx = 0 := UInt64.toBitVec_inj.mp zero
    have walk := historySteps_eventually fetch 2 _ _
      (scan_walk fetch agree first base s coverage preempt frame rxSection history events observed last)
    apply eventually_weaken (historyStep fetch) _ _ _ _ walk
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
    have walk := historySteps_eventually fetch 2 _ _
      (scan_walk fetch agree first base s coverage preempt frame rxSection history events observed last)
    apply eventually_trans (historyStep fetch) _ _ _ walk
    rintro t₁ ⟨af, machine₁, trace₁⟩
    have pc₁ : t₁.machine.pc = Image.Lookup.entry+0x34 := by
      simp [machine₁, walkExit, nonzero]
    have node₁ : t₁.machine.data.regs.rbx.toBitVec = a+8 := by
      rw [machine₁]; exact node
    have nodeRun := node_to_compare fetch agree tracePc traceCmp base t₁.machine.data coverage preempt
      trace₁.frame a e es node₁ (by rw [← node]; exact bucket) separate canCompare rxSection t₁.history
      (events ++ walkPoints rxSection s af) trace₁.observed (by rw [← pc₁]; exact trace₁.last)
    have cursor₁ : (⟨⟨t₁.machine.data, Image.Lookup.entry+0x34⟩, t₁.history⟩ : Executed) = t₁ := by rw [← pc₁]
    rw [cursor₁] at nodeRun
    apply eventually_trans (historyStep fetch) _ _ _ nodeRun
    rintro t₂ ⟨pc₂, bx₂, index₂, _, trace₂⟩
    have query₂ : (t₂.machine.data.regs.get (.low .r12 .W32)).toNat = query := by
      simpa only [Reg64s.get, Reg.base, Reg64s.get64, trace₂.frame.query] using queryReg
    have matchIndex : indexHit t₂.machine.data = (e.index == query) := by
      simp only [indexHit, index₂, query₂]
    have cmp := historySteps_eventually fetch 2 _ _
      (scan_compare fetch agree base t₂.machine.data coverage preempt trace₂.frame rxSection t₂.history
        (events ++ walkPoints rxSection s af) trace₂.observed (by rw [← pc₂]; exact trace₂.last))
    have cursor₂ : (⟨⟨t₂.machine.data, Image.Lookup.entry+0x59⟩, t₂.history⟩ : Executed) = t₂ := by rw [← pc₂]
    rw [cursor₂] at cmp
    apply eventually_trans (historyStep fetch) _ _ _ cmp
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
      have miss := scan_miss fetch agree tracePc base t₃.machine.data coverage preempt trace₃.frame
        a e es bx₃ (by rw [← node]; exact bucket) separate rxSection t₃.history
        ((events ++ walkPoints rxSection s af) ++ [cmpEvent]) trace₃.observed
        (by rw [← pc₃]; exact trace₃.last)
      have cursor₃ : (⟨⟨t₃.machine.data, Image.Lookup.entry+0x5e⟩, t₃.history⟩ : Executed) = t₃ := by rw [← pc₃]
      rw [cursor₃] at miss
      have suffix : Segment fetch (StableTrace base coverage preempt rxSection) t₃
          (fun seen t => ScanStop query es t.machine ∧ ∃ delta,
            seen = ((events ++ walkPoints rxSection s af) ++ [cmpEvent]) ++ delta ∧
            delta.filterMap (·.step) = scanSteps rxSection query es ∧ DecisionPoints delta) := by
        apply Segment.bind (fun first second => first.trans second) miss
        rintro t₄ seen ⟨same, next, pc₄, bx₄, baseTail, _⟩ trace₄
        subst seen
        have recur := ih (fun _ => canCompare) (fun cell member => separate cell (List.mem_cons_of_mem _ member)) false
          t₄.machine.data trace₄.frame (by rw [bx₄]; exact baseTail) t₄.history
          (((events ++ walkPoints rxSection s af) ++ [cmpEvent])) trace₄.observed
          (by change t₄.history.getLast? = some ⟨t₄.machine.data, Image.Lookup.entry+0x67⟩; rw [← pc₄]; exact trace₄.last)
        have cursor₄ : (⟨⟨t₄.machine.data, Image.Lookup.entry+0x67⟩, t₄.history⟩ : Executed) = t₄ := by rw [← pc₄]
        simp only [Bool.false_eq_true, ite_false] at recur
        rw [cursor₄] at recur
        apply eventually_weaken (historyStep fetch) _ _ _ _ recur
        rintro t₅ ⟨stop, delta, decisions, tags, trace₅⟩
        exact ⟨_, ⟨stop, delta, rfl, decisions, tags⟩, trace₅⟩
      apply eventually_weaken (historyStep fetch) _ _ _ _ suffix
      rintro t₅ ⟨seen, ⟨stop, delta, same, decisions, tags⟩, trace⟩
      subst seen
      refine ⟨?_, walkPoints rxSection s af ++ [cmpEvent] ++ delta, ?_,
        ((walk_decision_points rxSection s af).append (decision_point _ _ _ _)).append tags, ?_⟩
      · simpa only [ScanStop, firstIndex, hit, Bool.false_eq_true, ite_false] using stop
      · simp [scanSteps, hit, walkTrue, cmpEvent, matchIndex, LookupObservation.decision, decisions]
      · simpa only [List.append_assoc] using frontTrace.trans trace

/-- Recover the actual represented suffix of the first matching entry.
    Its cells remain members of the original bucket for byte separation. -/
theorem firstIndex_bucket (query : Nat) (memory : Mem 64)
    (es : List (Address × Leanux.WG.IndexEntry)) (head a : Address) (e : Leanux.WG.IndexEntry)
    (bucket : BucketShape memory head es) (found : firstIndex query es = some (a,e)) :
    ∃ rest, BucketShape memory (a+8) ((a,e)::rest) ∧
      ∀ cell ∈ (a,e)::rest, cell ∈ es := by
  induction es generalizing head with
  | nil => cases found
  | cons cell es ih =>
    rcases cell with ⟨b,f⟩
    cases hit : (f.index == query) with
    | true =>
      have same : (b,f) = (a,e) := by simpa only [firstIndex, hit, ite_true, Option.some.injEq] using found
      cases same
      refine ⟨es, ?_, fun _ member => member⟩
      have node := (bucket_cons_fields bucket).2.1
      rw [node] at bucket
      exact bucket
    | false =>
      have foundTail : firstIndex query es = some (a,e) := by
        simpa only [firstIndex, hit, Bool.false_eq_true, ite_false] using found
      obtain ⟨next, _, tail⟩ := bucket_tail _ _ _ _ _ bucket
      obtain ⟨rest, represented, members⟩ := ih next tail foundTail
      exact ⟨rest, represented, fun cell member => List.mem_cons_of_mem _ (members cell member)⟩

#print axioms firstIndex_bucket

#print axioms DecisionPoints.append
#print axioms walk_decision_points
#print axioms scan_search
end Binary.LookupHistory
