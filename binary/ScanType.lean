import ScanSearch

namespace Binary.LookupHistory
open TrustBase
local instance : Labels := Image.linkedLabels

/-- The register phase after the 32-bit kind-mask AND. Memory and every
    other fixed scan register have the original physical base values. -/
def kindBase (base : MachineData) (kind : UInt32) : MachineData :=
  base.setReg (.low .r14 .W32) (typeBits base kind)

theorem ScanFrame.masked {base s : MachineData} {coverage preempt}
    (frame : ScanFrame base coverage preempt s) (kind : UInt32) (af : Bool) :
    ScanFrame (kindBase base kind) coverage preempt (typeMasked s kind af) := by
  refine ⟨frame.ready.congr rfl rfl, frame.stack, frame.query, frame.output, ?_, frame.saved, frame.memory⟩
  simp only [kindBase, typeMasked, MachineData.setReg, Reg64s.set, Reg.base,
    Reg64s.set64, typeBits, Reg64s.get, Reg64s.get64, frame.kinds]

/-- Every successor after AND uses its exact overwritten R14 value. The
    incoming +9a state remains in the earlier phase; it is not re-labelled. -/
theorem scan_type_arguments (fetch : Int64 → Option Decoded) (agree : AnchoredDecoderAgreement fetch)
    (base s : MachineData) (kind : UInt32) (coverage : KcovLayout) (preempt : BitVec 32)
    (frame : ScanFrame base coverage preempt s)
    (field : s.dmem.loadInt (s.regs.rbx.toBitVec+24) 4 = some kind.toNat)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s, Image.Lookup.entry+0x9a⟩) :
    historySteps fetch 3 (fun t => ∃ af,
      t.machine = ⟨typeArguments s kind af, Image.Lookup.entry+0xa3⟩ ∧
      ScanTrace (kindBase base kind) coverage preempt rxSection history events t)
      ⟨⟨s, Image.Lookup.entry+0x9a⟩, history⟩ := by
  apply historySteps_mono fetch 3 _ _ _ _ (type_arguments fetch agree s kind history field)
  rintro t ⟨af₁, af₂, machine, recorded⟩
  have frame₁ := frame.masked kind af₁
  have frame₂ : ScanFrame (kindBase base kind) coverage preempt
      (argumentZero (typeMasked s kind af₁) af₂) := by
    apply frame₁.congr <;> rfl
  have frame₃ : ScanFrame (kindBase base kind) coverage preempt (typeArguments s kind af₂) := by
    apply (frame.masked kind false).congr <;> rfl
  refine ⟨af₂, machine, ScanTrace.of_suffix observed last _ recorded ?_ ?_ ?_ ?_⟩
  · simpa only [machine] using frame₃
  · simp [machine]
  · simp [observeHistory, LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]
  · intro q member _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact frame₁
    · exact frame₂
    · exact frame₃

/-- The terminal kind guard emits both source decisions, in their original
    order, at the same actual machine state. -/
theorem scan_type_guard (fetch : Int64 → Option Decoded) (agree : AnchoredDecoderAgreement fetch)
    (base s : MachineData) (coverage : KcovLayout) (preempt : BitVec 32)
    (frame : ScanFrame base coverage preempt s)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s, Image.Lookup.entry+0xa8⟩) :
    historySteps fetch 2 (fun t => ∃ af,
      t.machine = typeExit s af ∧
      ScanTrace base coverage preempt rxSection history
        (events ++ [LookupObservation.decision rxSection .idxTypeMatch
          (decide (s.regs.get (.low .r14 .W32) ≠ 0)) t.machine,
          LookupObservation.decision rxSection .idxFound
          (decide (s.regs.get (.low .r14 .W32) ≠ 0)) t.machine]) t)
      ⟨⟨s, Image.Lookup.entry+0xa8⟩, history⟩ := by
  apply historySteps_mono fetch 2 _ _ _ _ (type_guard fetch agree s history)
  rintro t ⟨af, machine, recorded⟩
  have endpoint : t.machine = typeExit s af := machine
  have nextFrame : ScanFrame base coverage preempt (tested (.low .r14 .W32) s af) :=
    frame.congr rfl rfl rfl rfl rfl rfl
  refine ⟨af, endpoint, ScanTrace.of_observed_suffix observed last _ recorded ?_ ?_ _ ?_ ?_⟩
  · simpa only [endpoint, typeExit] using nextFrame
  · simp [endpoint, typeExit]
  · simpa only [endpoint, typeExit] using type_guard_observation rxSection s af
  · intro q member _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact nextFrame

theorem kindBase_value (base : MachineData) (kind : UInt32) :
    (kindBase base kind).regs.get (.low .r14 .W32) = typeBits base kind := by
  simp [kindBase, MachineData.setReg, Reg64s.set, Reg64s.set64,
    Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop, BitVec.take]
  rw [BitVec.extractLsb'_setWidth_of_le (by decide)]
  simp

/-- From the first matching index to either kind exit. The two physical
    register phases are kept as consecutive actual history segments. A
    rejected kind still has RBX=a here; the later XOR has not run yet. -/
theorem matched_type_exit (fetch : Int64 → Option Decoded) (agree : AnchoredDecoderAgreement fetch)
    (tracePc : TracePcContract fetch) (traceCmp : TraceConstCmp4Contract fetch)
    (base s : MachineData) (coverage : KcovLayout) (preempt : BitVec 32)
    (frame : ScanFrame base coverage preempt s)
    (a : Address) (e : Leanux.WG.IndexEntry) (rest : List (Address × Leanux.WG.IndexEntry))
    (cursor : s.regs.rbx.toBitVec = a)
    (bucket : BucketShape base.dmem (a+8) ((a,e)::rest))
    (separate : ∀ cell ∈ (a,e)::rest, ∀ address, BucketShapeReads cell.1 address →
      ¬scanWrites base coverage address)
    (kinds : List Leanux.WG.IndexKind) (mask : KindMask (base.regs.get (.low .r14 .W32)) kinds)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s, Image.Lookup.entry+0x95⟩) :
    Eventually (historyStep fetch) (fun t =>
      t.machine.pc = (if kinds.contains e.kind then Image.Lookup.entry+0xad else Image.Lookup.entry+0x71) ∧
      t.machine.data.regs.rbx.toBitVec = a ∧
      ScanFrame (kindBase base (.ofBitVec (kindWord e.kind))) coverage preempt t.machine.data ∧
      observeHistory (LookupObservation.edge rxSection) t.history =
        .ok (events ++ [LookupObservation.decision rxSection .idxTypeMatch (kinds.contains e.kind) t.machine,
          LookupObservation.decision rxSection .idxFound (kinds.contains e.kind) t.machine]) ∧
      t.history.getLast? = some t.machine ∧
      ∃ before after, t.history = history ++ before ++ after ∧
        ScanCuts base coverage preempt before ∧
        ScanCuts (kindBase base (.ofBitVec (kindWord e.kind))) coverage preempt after ∧
        ∃ boundary, (history ++ before).getLast? = some boundary ∧
          boundary.pc = Image.Lookup.entry+0x9a ∧ ScanFrame base coverage preempt boundary.data)
      ⟨⟨s, Image.Lookup.entry+0x95⟩, history⟩ := by
  let kind := UInt32.ofBitVec (kindWord e.kind)
  have call := scan_call_cursor fetch "L_ffffffff810f3100"
    ⟨⟨s, Image.Lookup.entry+0x95⟩, history⟩ (agree _ _ (by rfl)) .pc tracePc base coverage preempt
    frame rxSection events observed last (by
      simp [LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
  apply eventually_trans (historyStep fetch) _ _ _ call
  rintro t₁ ⟨pc₁, bx₁, _, trace₁⟩
  change t₁.machine.pc = Image.Lookup.entry+0x9a at pc₁
  have currentBucket := trace₁.frame.bucket (a+8) ((a,e)::rest) bucket separate
  have field : t₁.machine.data.dmem.loadInt (t₁.machine.data.regs.rbx.toBitVec+24) 4 = some kind.toNat := by
    rw [bx₁, cursor]
    exact (bucket_cons_fields currentBucket).2.2.2.1
  have args := historySteps_eventually fetch 3 _ _
    (scan_type_arguments fetch agree base t₁.machine.data kind coverage preempt trace₁.frame field
      rxSection t₁.history events trace₁.observed (by rw [← pc₁]; exact trace₁.last))
  have cursor₁ : (⟨⟨t₁.machine.data, Image.Lookup.entry+0x9a⟩, t₁.history⟩ : Executed) = t₁ := by rw [← pc₁]
  rw [cursor₁] at args
  apply eventually_trans (historyStep fetch) _ _ _ args
  rintro t₂ ⟨af, machine₂, trace₂⟩
  have pc₂ : t₂.machine.pc = Image.Lookup.entry+0xa3 := congrArg MachineState.pc machine₂
  have cmpCall := scan_call_cursor fetch "L_ffffffff810f3f00" t₂
    (by rw [pc₂]; exact agree _ _ (by rfl)) .constCmp4 traceCmp (kindBase base kind) coverage preempt
    trace₂.frame rxSection events trace₂.observed trace₂.last (by
      simp [LookupObservation.edge, pc₂, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
  apply eventually_trans (historyStep fetch) _ _ _ cmpCall
  rintro t₃ ⟨pc₃, bx₃, _, trace₃⟩
  rw [pc₂] at pc₃
  change t₃.machine.pc = Image.Lookup.entry+0xa8 at pc₃
  have typeReg : t₃.machine.data.regs.get (.low .r14 .W32) = typeBits base kind := by
    have same : t₃.machine.data.regs.get (.low .r14 .W32) =
        (kindBase base kind).regs.get (.low .r14 .W32) := by
      simp only [Reg64s.get, Reg.base, Reg64s.get64, trace₃.frame.kinds]
    exact same.trans (kindBase_value base kind)
  have accepted : decide (t₃.machine.data.regs.get (.low .r14 .W32) ≠ 0) = kinds.contains e.kind := by
    rw [typeReg]
    exact type_source base e.kind kinds mask
  have guard := historySteps_eventually fetch 2 _ _
    (scan_type_guard fetch agree (kindBase base kind) t₃.machine.data coverage preempt trace₃.frame
      rxSection t₃.history events trace₃.observed (by rw [← pc₃]; exact trace₃.last))
  have cursor₃ : (⟨⟨t₃.machine.data, Image.Lookup.entry+0xa8⟩, t₃.history⟩ : Executed) = t₃ := by rw [← pc₃]
  rw [cursor₃] at guard
  apply eventually_weaken (historyStep fetch) _ _ _ _ guard
  rintro t₄ ⟨af₄, machine₄, trace₄⟩
  have suffix := trace₂.trans (trace₃.trans trace₄)
  obtain ⟨before, beforeEq, beforeCuts⟩ := trace₁.extension
  obtain ⟨after, afterEq, afterCuts⟩ := suffix.extension
  refine ⟨?_, ?_, suffix.frame, ?_, suffix.last, before, after, ?_, beforeCuts, afterCuts,
    t₁.machine, ?_, pc₁, trace₁.frame⟩
  · rw [machine₄]
    change (if t₃.machine.data.regs.get (.low .r14 .W32) == 0 then _ else _) = _
    by_cases zero : t₃.machine.data.regs.get (.low .r14 .W32) = 0#32
    · have rejected : kinds.contains e.kind = false := by simpa [zero] using accepted.symm
      simp [zero, rejected]
    · have good : kinds.contains e.kind = true := by simpa [zero] using accepted.symm
      simp [zero, good]
  · rw [machine₄]
    change t₃.machine.data.regs.rbx.toBitVec = a
    rw [bx₃, machine₂]
    change t₁.machine.data.regs.rbx.toBitVec = a
    rw [bx₁, cursor]
  · simpa only [accepted] using suffix.observed
  · rw [afterEq, beforeEq]
  · rw [← beforeEq]
    exact trace₁.last

#print axioms kindBase_value
#print axioms matched_type_exit

#print axioms ScanFrame.masked
#print axioms scan_type_arguments
#print axioms scan_type_guard
end Binary.LookupHistory
