import ScanNode

namespace Binary.LookupHistory
open TrustBase
local instance : Labels := Image.linkedLabels

/-- Both loop headers execute the same source walk decision. The empty
    case also emits the compiler-merged found=false event. -/
theorem scan_walk (fetch : Int64 → Option Decoded) (agree : AnchoredDecoderAgreement fetch)
    (first : Bool) (base s : MachineData) (coverage : KcovLayout) (preempt : BitVec 32)
    (frame : ScanFrame base coverage preempt s)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s, Image.Lookup.entry+(if first then 0x2f else 0x67)⟩) :
    historySteps fetch 2 (fun t => ∃ af,
      t.machine = walkExit s af ∧
      ScanTrace base coverage preempt rxSection history (events ++ walkPoints rxSection s af) t)
      ⟨⟨s, Image.Lookup.entry+(if first then 0x2f else 0x67)⟩, history⟩ := by
  have run : historySteps fetch 2 (TestHistory (.low .rbx .W64) s
      (Image.Lookup.entry+(if first then 0x32 else 0x6a)) (walkExit s false).pc history)
      ⟨⟨s, Image.Lookup.entry+(if first then 0x2f else 0x67)⟩, history⟩ := by
    cases first
    · exact next_bucket_guard fetch agree s history
    · exact first_bucket_guard fetch agree s history
  apply historySteps_mono fetch 2 _ _ _ _ run
  rintro t ⟨af, machine, recorded⟩
  have endpoint : t.machine = walkExit s af := machine
  have nextFrame : ScanFrame base coverage preempt (tested (.low .rbx .W64) s af) :=
    frame.congr rfl rfl rfl rfl rfl rfl
  refine ⟨af, endpoint, ScanTrace.of_observed_suffix observed last _ recorded ?_ ?_
    (walkPoints rxSection s af) ?_ ?_⟩
  · simpa only [endpoint, walkExit] using nextFrame
  · simp only [List.getLast?_cons_cons, List.getLast?_singleton]
    exact congrArg some machine.symm
  · cases first
    · exact next_walk_observation rxSection s af
    · exact first_walk_observation rxSection s af
  · intro q member _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact nextFrame

/-- The index guard appends its actual decision instead of keeping an
    unchanged event list across a semantic branch. -/
theorem scan_compare (fetch : Int64 → Option Decoded) (agree : AnchoredDecoderAgreement fetch)
    (base s : MachineData) (coverage : KcovLayout) (preempt : BitVec 32)
    (frame : ScanFrame base coverage preempt s)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s, Image.Lookup.entry+0x59⟩) :
    historySteps fetch 2 (fun t => t.machine = compareExit s ∧
      ScanTrace base coverage preempt rxSection history
        (events ++ [LookupObservation.decision rxSection .idxMatch (indexHit s) (compareExit s)]) t)
      ⟨⟨s, Image.Lookup.entry+0x59⟩, history⟩ := by
  apply historySteps_mono fetch 2 _ _ _ _ (index_compare fetch agree s history)
  rintro t ⟨machine, recorded⟩
  have nextFrame : ScanFrame base coverage preempt (compared s) :=
    frame.congr rfl rfl rfl rfl rfl rfl
  refine ⟨machine, ScanTrace.of_observed_suffix observed last _ recorded ?_ ?_ _
    (index_compare_observation rxSection s) ?_⟩
  · simpa only [machine, compareExit] using nextFrame
  · simp [machine]
  · intro q member _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact nextFrame

/-- The actual tail-pointer load preserves the scan frame and records its
    successor at the recursive loop header. -/
theorem scan_next (fetch : Int64 → Option Decoded) (agree : AnchoredDecoderAgreement fetch)
    (base s : MachineData) (next : UInt64) (coverage : KcovLayout) (preempt : BitVec 32)
    (frame : ScanFrame base coverage preempt s)
    (loaded : s.dmem.loadInt (s.regs.rbx.toBitVec+8) 8 = some next.toNat)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s, Image.Lookup.entry+0x63⟩) :
    historySteps fetch 1 (fun t =>
      t.machine = ⟨nextData s next, Image.Lookup.entry+0x67⟩ ∧
      ScanTrace base coverage preempt rxSection history events t)
      ⟨⟨s, Image.Lookup.entry+0x63⟩, history⟩ := by
  apply historySteps_mono fetch 1 _ _ _ _ (next_load fetch agree s next history loaded)
  rintro t ⟨machine, recorded⟩
  have nextFrame : ScanFrame base coverage preempt (nextData s next) :=
    frame.congr rfl rfl rfl rfl rfl rfl
  refine ⟨machine, ScanTrace.of_suffix observed last _ recorded ?_ (by simp) ?_ ?_⟩
  · simpa only [machine] using nextFrame
  · rw [machine]
    simp [observeHistory, LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]
  · intro q member _
    have eq := List.mem_singleton.mp member
    simpa only [eq, machine] using nextFrame

/-- A missed node returns to the actual recursive header. The remaining
    chain is established in the fixed incoming memory as well as in the
    current memory, so the induction does not assume a fresh bucket. -/
theorem scan_miss (fetch : Int64 → Option Decoded) (agree : AnchoredDecoderAgreement fetch)
    (tracePc : TracePcContract fetch)
    (base s : MachineData) (coverage : KcovLayout) (preempt : BitVec 32)
    (frame : ScanFrame base coverage preempt s)
    (a : Address) (e : Leanux.WG.IndexEntry) (rest : List (Address × Leanux.WG.IndexEntry))
    (cursor : s.regs.rbx.toBitVec = a)
    (bucket : BucketShape base.dmem (a+8) ((a,e)::rest))
    (separate : ∀ cell ∈ (a,e)::rest, ∀ address, BucketShapeReads cell.1 address →
      ¬scanWrites base coverage address)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s, Image.Lookup.entry+0x5e⟩) :
    Eventually (historyStep fetch) (fun t => ∃ next : UInt64,
      t.machine.pc = Image.Lookup.entry+0x67 ∧ t.machine.data.regs.rbx = next ∧
      BucketShape base.dmem next.toBitVec rest ∧
      BucketShape t.machine.data.dmem next.toBitVec rest ∧
      ScanTrace base coverage preempt rxSection history events t)
      ⟨⟨s, Image.Lookup.entry+0x5e⟩, history⟩ := by
  have call := scan_call_cursor fetch "L_ffffffff810f3100"
    ⟨⟨s, Image.Lookup.entry+0x5e⟩, history⟩ (agree _ _ (by rfl)) .pc tracePc base coverage preempt
    frame rxSection events observed last (by
      simp [LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
  apply eventually_trans (historyStep fetch) _ _ _ call
  rintro t₁ ⟨pc₁, bx₁, _, trace₁⟩
  change t₁.machine.pc = Image.Lookup.entry+0x63 at pc₁
  have currentBucket := trace₁.frame.bucket (a+8) ((a,e)::rest) bucket separate
  obtain ⟨next, loaded, tail⟩ := bucket_tail _ _ _ _ _ currentBucket
  simp only [Layouts.node_next, BitVec.add_zero] at loaded
  have field : t₁.machine.data.dmem.loadInt (t₁.machine.data.regs.rbx.toBitVec+8) 8 =
      some (UInt64.ofBitVec next).toNat := by
    rw [bx₁, cursor]
    exact loaded
  have baseTail : BucketShape base.dmem next rest :=
    BucketShape.frame_reads (fun address outside => (trace₁.frame.memory address outside).symm)
      rest (fun cell member => separate cell (List.mem_cons_of_mem _ member)) next tail
  have load := historySteps_eventually fetch 1 _ _
    (scan_next fetch agree base t₁.machine.data (.ofBitVec next) coverage preempt trace₁.frame field
      rxSection t₁.history events trace₁.observed (by rw [← pc₁]; exact trace₁.last))
  have initial : (⟨⟨t₁.machine.data, Image.Lookup.entry+0x63⟩, t₁.history⟩ : Executed) = t₁ := by rw [← pc₁]
  rw [initial] at load
  apply eventually_weaken (historyStep fetch) _ _ _ _ load
  rintro t₂ ⟨machine₂, trace₂⟩
  refine ⟨.ofBitVec next, congrArg MachineState.pc machine₂, ?_, baseTail, ?_, trace₁.trans trace₂⟩
  · rw [machine₂]; rfl
  · rw [machine₂]
    exact tail

#print axioms scan_miss

#print axioms scan_walk
#print axioms scan_compare
#print axioms scan_next
end Binary.LookupHistory
