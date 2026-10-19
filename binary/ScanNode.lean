import ScanFrame

namespace Binary.LookupHistory
open TrustBase
local instance : Labels := Image.linkedLabels

theorem scan_container (fetch : Int64 → Option Decoded) (agree : AnchoredDecoderAgreement fetch)
    (base s : MachineData) (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (frame : ScanFrame base coverage preempt s)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s, Image.Lookup.entry+0x39⟩) :
    historySteps fetch 1 (fun t =>
      t.machine = ⟨containerData s, Image.Lookup.entry+0x3d⟩ ∧
      StableTrace base coverage preempt rxSection history events t)
      ⟨⟨s, Image.Lookup.entry+0x39⟩, history⟩ := by
  apply historySteps_mono fetch 1 _ _ _ _ (container_sub fetch agree s history)
  rintro t ⟨machine, recorded⟩
  have fields := container_sub_shape s
  have nextFrame : ScanFrame base coverage preempt (containerData s) := by
    apply frame.congr fields.1
    all_goals rw [fields.2]
  refine ⟨machine, StableTrace.of_suffix observed last [t.machine] recorded ?_ (by simp) ?_ ?_⟩
  · simpa only [machine] using nextFrame
  · rw [machine]
    simp [observeHistory, LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]
  · intro q member _
    have eq := List.mem_singleton.mp member
    simpa only [eq, machine] using nextFrame

theorem scan_entry_guard (fetch : Int64 → Option Decoded) (agree : AnchoredDecoderAgreement fetch)
    (base s : MachineData) (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (frame : ScanFrame base coverage preempt s)
    (nonnull : s.regs.get (.low .rbx .W64) ≠ 0#64)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s, Image.Lookup.entry+0x42⟩) :
    historySteps fetch 2 (fun t => ∃ af,
      t.machine = ⟨tested (.low .rbx .W64) s af, Image.Lookup.entry+0x47⟩ ∧
      StableTrace base coverage preempt rxSection history events t)
      ⟨⟨s, Image.Lookup.entry+0x42⟩, history⟩ := by
  apply historySteps_mono fetch 2 _ _ _ _ (entry_guard fetch agree s history)
  rintro t ⟨af, machine, recorded⟩
  have jump : (if s.regs.get (.low .rbx .W64) == 0 then Image.Lookup.entry+0x71
      else Image.Lookup.entry+0x47) = Image.Lookup.entry+0x47 := by simp [nonnull]
  rw [jump] at machine recorded
  have nextFrame : ScanFrame base coverage preempt (tested (.low .rbx .W64) s af) :=
    frame.congr rfl rfl rfl rfl rfl rfl
  refine ⟨af, machine, StableTrace.of_suffix observed last _ recorded ?_ ?_ ?_ ?_⟩
  · simpa only [machine] using nextFrame
  · simp [machine]
  · simp [observeHistory, LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]
  · intro q member _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact nextFrame

theorem scan_index_arguments (fetch : Int64 → Option Decoded) (agree : AnchoredDecoderAgreement fetch)
    (base s : MachineData) (index : UInt32) (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (frame : ScanFrame base coverage preempt s)
    (field : s.dmem.loadInt (s.regs.rbx.toBitVec+28) 4 = some index.toNat)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s, Image.Lookup.entry+0x4c⟩) :
    historySteps fetch 3 (fun t =>
      t.machine = ⟨indexArgs2 s index, Image.Lookup.entry+0x54⟩ ∧
      StableTrace base coverage preempt rxSection history events t)
      ⟨⟨s, Image.Lookup.entry+0x4c⟩, history⟩ := by
  have frame₁ : ScanFrame base coverage preempt (indexLoaded s index) := by
    apply frame.congr <;> rfl
  have frame₂ : ScanFrame base coverage preempt (indexArgs1 s index) := by
    apply frame₁.congr <;> rfl
  have frame₃ : ScanFrame base coverage preempt (indexArgs2 s index) := by
    apply frame₂.congr <;> rfl
  apply historySteps_mono fetch 3 _ _ _ _ (index_arguments fetch agree s index history field)
  rintro t ⟨machine, recorded⟩
  refine ⟨machine, StableTrace.of_suffix observed last _ recorded ?_ ?_ ?_ ?_⟩
  · simpa only [machine] using frame₃
  · simp [machine]
  · exact index_arguments_observation rxSection s index
  · intro q member _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact frame₁
    · exact frame₂
    · exact frame₃

/-- One nonempty bucket node, from after walk=true to the index comparison.
    This composes four actual calls and all intervening instructions, with
    the physical invariant at every appended anchored cut. -/
theorem node_to_compare (fetch : Int64 → Option Decoded) (agree : AnchoredDecoderAgreement fetch)
    (tracePc : TracePcContract fetch) (traceCmp : TraceCmp4Contract fetch)
    (base s : MachineData) (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (frame : ScanFrame base coverage preempt s)
    (a : Address) (e : Leanux.WG.IndexEntry) (rest : List (Address × Leanux.WG.IndexEntry))
    (node : s.regs.rbx.toBitVec = a+8)
    (bucket : BucketShape base.dmem (a+8) ((a,e)::rest))
    (separate : ∀ cell ∈ (a,e)::rest, ∀ address, BucketShapeReads cell.1 address →
      ¬scanWrites base coverage address)
    (comparison : coverage.CompareAllowed preempt)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s, Image.Lookup.entry+0x34⟩) :
    Eventually (historyStep fetch) (fun t =>
      t.machine.pc = Image.Lookup.entry+0x59 ∧ t.machine.data.regs.rbx.toBitVec = a ∧
      (t.machine.data.regs.get (.low .rbp .W32)).toNat = e.index ∧
      BucketShape t.machine.data.dmem (a+8) ((a,e)::rest) ∧
      StableTrace base coverage preempt rxSection history events t)
      ⟨⟨s, Image.Lookup.entry+0x34⟩, history⟩ := by
  have first := scan_call_cursor fetch "L_ffffffff810f3100"
    ⟨⟨s, Image.Lookup.entry+0x34⟩, history⟩ (agree _ _ (by rfl)) .pc tracePc base coverage preempt
    frame (frame).ready.pc_allowed
    rxSection events observed last (by
      simp [LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
  apply eventually_trans (historyStep fetch) _ _ _ first
  rintro t₁ ⟨pc₁, bx₁, _, trace₁⟩
  change t₁.machine.pc = Image.Lookup.entry+0x39 at pc₁
  have sub := historySteps_eventually fetch 1 _ _
    (scan_container fetch agree base t₁.machine.data coverage preempt trace₁.frame rxSection
      t₁.history events trace₁.observed (by rw [← pc₁]; exact trace₁.last))
  have cursor₁ : (⟨⟨t₁.machine.data, Image.Lookup.entry+0x39⟩, t₁.history⟩ : Executed) = t₁ := by
    rw [← pc₁]
  rw [cursor₁] at sub
  apply eventually_trans (historyStep fetch) _ _ _ sub
  rintro t₂ ⟨machine₂, trace₂⟩
  have pc₂ : t₂.machine.pc = Image.Lookup.entry+0x3d := congrArg MachineState.pc machine₂
  have bx₂ : t₂.machine.data.regs.rbx.toBitVec = a := by
    rw [machine₂, (container_sub_shape t₁.machine.data).2, bx₁]
    change s.regs.rbx.toBitVec-8 = a
    rw [node, BitVec.add_sub_cancel]
  have second := scan_call_cursor fetch "L_ffffffff810f3100" t₂
    (by rw [pc₂]; exact agree _ _ (by rfl)) .pc tracePc base coverage preempt trace₂.frame (trace₂.frame).ready.pc_allowed
    rxSection events trace₂.observed trace₂.last (by
      simp [LookupObservation.edge, pc₂, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
  apply eventually_trans (historyStep fetch) _ _ _ second
  rintro t₃ ⟨pc₃, bx₃, _, trace₃⟩
  rw [pc₂] at pc₃
  change t₃.machine.pc = Image.Lookup.entry+0x42 at pc₃
  have nonnull : t₃.machine.data.regs.get (.low .rbx .W64) ≠ 0#64 := by
    have actual : t₃.machine.data.regs.rbx.toBitVec = a := by rw [bx₃, bx₂]
    simpa [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop, BitVec.take, actual]
      using (bucket_cons_fields bucket).1
  have guard := historySteps_eventually fetch 2 _ _
    (scan_entry_guard fetch agree base t₃.machine.data coverage preempt trace₃.frame nonnull
      rxSection t₃.history events trace₃.observed (by rw [← pc₃]; exact trace₃.last))
  have cursor₃ : (⟨⟨t₃.machine.data, Image.Lookup.entry+0x42⟩, t₃.history⟩ : Executed) = t₃ := by rw [← pc₃]
  rw [cursor₃] at guard
  apply eventually_trans (historyStep fetch) _ _ _ guard
  rintro t₄ ⟨af, machine₄, trace₄⟩
  have pc₄ : t₄.machine.pc = Image.Lookup.entry+0x47 := congrArg MachineState.pc machine₄
  have bx₄ : t₄.machine.data.regs.rbx.toBitVec = a := by
    rw [machine₄]
    change t₃.machine.data.regs.rbx.toBitVec = a
    rw [bx₃, bx₂]
  have third := scan_call_cursor fetch "L_ffffffff810f3100" t₄
    (by rw [pc₄]; exact agree _ _ (by rfl)) .pc tracePc base coverage preempt trace₄.frame (trace₄.frame).ready.pc_allowed
    rxSection events trace₄.observed trace₄.last (by
      simp [LookupObservation.edge, pc₄, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
  apply eventually_trans (historyStep fetch) _ _ _ third
  rintro t₅ ⟨pc₅, bx₅, _, trace₅⟩
  rw [pc₄] at pc₅
  change t₅.machine.pc = Image.Lookup.entry+0x4c at pc₅
  have currentBucket := trace₅.frame.bucket (a+8) ((a,e)::rest) bucket separate
  have fields := bucket_cons_fields currentBucket
  let index := UInt32.ofNat e.index
  have indexNat : index.toNat = e.index := by
    simp only [index]
    exact Nat.mod_eq_of_lt fields.2.2.1
  have loaded : t₅.machine.data.dmem.loadInt (t₅.machine.data.regs.rbx.toBitVec+28) 4 = some index.toNat := by
    rw [bx₅, bx₄, indexNat]
    exact fields.2.2.2.2
  have args := historySteps_eventually fetch 3 _ _
    (scan_index_arguments fetch agree base t₅.machine.data index coverage preempt trace₅.frame loaded
      rxSection t₅.history events trace₅.observed (by rw [← pc₅]; exact trace₅.last))
  have cursor₅ : (⟨⟨t₅.machine.data, Image.Lookup.entry+0x4c⟩, t₅.history⟩ : Executed) = t₅ := by rw [← pc₅]
  rw [cursor₅] at args
  apply eventually_trans (historyStep fetch) _ _ _ args
  rintro t₆ ⟨machine₆, trace₆⟩
  have pc₆ : t₆.machine.pc = Image.Lookup.entry+0x54 := congrArg MachineState.pc machine₆
  have fourth := scan_call_cursor fetch "L_ffffffff810f3e80" t₆
    (by rw [pc₆]; exact agree _ _ (by rfl)) .cmp4 traceCmp base coverage preempt trace₆.frame (LookupCoverage.compare_allowed comparison (by decide))
    rxSection events trace₆.observed trace₆.last (by
      simp [LookupObservation.edge, pc₆, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
  apply eventually_weaken (historyStep fetch) _ _ _ _ fourth
  rintro t₇ ⟨pc₇, bx₇, bp₇, trace₇⟩
  refine ⟨by rw [pc₇, pc₆]; rfl, ?_, ?_, trace₇.frame.bucket _ _ bucket separate,
    trace₁.trans (trace₂.trans (trace₃.trans (trace₄.trans (trace₅.trans (trace₆.trans trace₇)))))⟩
  · rw [bx₇, machine₆]
    change t₅.machine.data.regs.rbx.toBitVec = a
    rw [bx₅, bx₄]
  · have bp : t₇.machine.data.regs.get (.low .rbp .W32) = index.toBitVec := by
      simp [Reg64s.get, Reg64s.get64, bp₇, machine₆, indexArgs2, indexArgs1, indexLoaded,
        MachineData.setReg, Reg64s.set, Reg64s.set64, Reg.base, Reg.offset, BitVec.drop, BitVec.take]
      rw [BitVec.extractLsb'_setWidth_of_le (by decide)]
      simp
    rw [bp]
    exact indexNat

#print axioms node_to_compare

#print axioms scan_container
#print axioms scan_entry_guard
#print axioms scan_index_arguments
end Binary.LookupHistory
