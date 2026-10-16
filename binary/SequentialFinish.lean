import SequentialPrepared
import LookupBhHistory
import LookupReturnHistory

namespace Binary.Sequential
open Leanux Leanux.WG TrustBase LookupRelation LookupHistory LookupObservation
local instance : Labels := Image.linkedLabels

/-- A real CALL/service/RET segment, forgetting its internal trace. -/
theorem callback (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (tracePc : TracePcContract fetch)
    (current : Executed) (offset : Nat)
    (site : offset = 0x6c ∨ offset = 0x73 ∨ offset = 0xc5)
    (pc : current.machine.pc = Image.Lookup.entry + .ofNat offset)
    (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (ready : LookupCoverage.CallsReady coverage preempt current.machine.data) :
    Eventually (historyStep fetch) (fun t =>
      t.machine.pc = current.machine.pc+5 ∧
      t.machine.data.regs.rbx = current.machine.data.regs.rbx ∧
      t.machine.data.regs.rbp = current.machine.data.regs.rbp ∧
      ScanFrame current.machine.data coverage preempt t.machine.data) current := by
  have run := LookupInstrumentation.observed_call fetch current.machine.pc "L_ffffffff810f3100"
    (by rw [pc]; rcases site with rfl | rfl | rfl <;> exact agree _ _ (by rfl))
    .pc tracePc current.machine.data coverage preempt ready ready.pc_allowed
    0 [] [] [] rfl (by
      rcases site with rfl | rfl | rfl <;>
        simp [pc, LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry] <;> rfl)
  have endpoint : Eventually (instructionStep fetch) (fun t =>
      t.pc = current.machine.pc+5 ∧ t.data.regs.rbx = current.machine.data.regs.rbx ∧
      t.data.regs.rbp = current.machine.data.regs.rbp ∧
      ScanFrame current.machine.data coverage preempt t.data) current.machine := by
    apply forget run
    rintro t ⟨ret, ready, frame, _⟩
    obtain ⟨pc, sp, bx, bp, r12, r13, r14, r15⟩ := Instrumentation.returned_caller _ _ _ _ ret
    exact ⟨pc, bx, bp, ready, sp, r12, r13, r14, r15, frame⟩
  exact history_lift fetch _ _ endpoint current.history

theorem return_from_saved (fetch : Int64 → Option Decoded) (agree : AnchoredDecoderAgreement fetch)
    (entry current : MachineData) (returnAddress : UInt64)
    (saved : OuterSaved entry current)
    (returnWord : entry.dmem.loadInt entry.regs.rsp.toBitVec 8 = some (returnAddress.toNat : Int))
    (history : List MachineState) :
    historySteps fetch 7 (fun final =>
      Returned ⟨entry, Image.Lookup.entry⟩ final.machine returnAddress ∧
      final.machine.data.regs.rax = current.regs.rbx ∧
      final.machine.data.dmem = current.dmem)
      ⟨⟨current, Image.Lookup.entry+0x89⟩, history⟩ := by
  have loads := saved.loads entry current returnAddress returnWord
  have run := LookupReturn.epilogue_history fetch agree current history
    entry.regs.rbx entry.regs.rbp entry.regs.r12 entry.regs.r13 entry.regs.r14 returnAddress
    (by simpa [outerWords] using loads 0 (by decide))
    (by simpa [outerWords] using loads 1 (by decide))
    (by simpa [outerWords] using loads 2 (by decide))
    (by simpa [outerWords] using loads 3 (by decide))
    (by simpa [outerWords] using loads 4 (by decide))
    (by simpa [outerWords] using loads 5 (by decide))
  apply historySteps_mono fetch 7 _ _ _ _ run
  rintro final ⟨machine, _⟩
  refine ⟨?_, by rw [machine]; rfl, by rw [machine]; rfl⟩
  rw [machine]
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, saved.saved⟩
  change current.regs.rsp+48 = entry.regs.rsp+8
  rw [saved.stack]
  apply UInt64.toBitVec_inj.mp
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_sub]
  change entry.regs.rsp.toBitVec-40+48 = entry.regs.rsp.toBitVec+8
  rw [show (48 : BitVec 64) = 40+8 from rfl, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem common_finish (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (tracePc : TracePcContract fetch) (bh : BhEnableContract fetch)
    (c : Config) (coverage : KcovLayout) (preempt : BitVec 32) (ra : UInt64)
    (s : MachineData) (world : World) (v : View)
    (entry : LookupEntry c coverage preempt ra ⟨s, Image.Lookup.entry⟩ world v)
    (current : Executed) (pc : current.machine.pc = Image.Lookup.entry+0x73)
    (saved : OuterSaved s current.machine.data)
    (ready : LookupCoverage.CallsReady ⟨coverage, preempt, v⟩ (512+preempt) current.machine.data)
    (pending : LookupPendingRead preempt → current.machine.data.dmem.loadInt softirqPendingAddress 2 = some 0) :
    Eventually (historyStep fetch) (fun final =>
      Returned ⟨s, Image.Lookup.entry⟩ final.machine ra ∧
      final.machine.data.regs.rax = current.machine.data.regs.rbx ∧
      EqualOutside (fun a => scanWrites current.machine.data ⟨coverage, preempt, v⟩ a ∨
        InRange preemptCountAddress 4 a) current.machine.data.dmem final.machine.data.dmem ∧
      LookupCoverageAt coverage preempt v final.machine.data.dmem ∧
      load32 final.machine.data.dmem preemptCountAddress = some preempt) current := by
  have run := callback fetch agree tracePc current 0x73 (.inr (.inl rfl)) pc
    ⟨coverage, preempt, v⟩ (512+preempt) ready
  apply eventually_trans (historyStep fetch) _ _ _ run
  rintro callback ⟨cbPC, cbBX, cbBP, traced⟩
  have callbackPC : callback.machine.pc = Image.Lookup.entry+0x78 := by simpa only [pc, show Image.Lookup.entry+0x73+5 = Image.Lookup.entry+0x78 from rfl] using cbPC
  have cbSaved := saved.frame traced.stack traced.saved _ traced.memory (by
    intro a inside written
    rcases written with stack | covered
    · apply outer_callback_apart s a inside
      simpa only [saved.stack, UInt64.toBitVec_sub, BitVec.sub_sub,
        show (40 : UInt64).toBitVec+8 = (48 : BitVec 64) from rfl] using stack
    · exact entry.coverageStack a covered (outer_live c s a inside))
  have cbPending : LookupPendingRead preempt → callback.machine.data.dmem.loadInt softirqPendingAddress 2 = some 0 := by
    intro need
    have read := traced.memory.loadInt softirqPendingAddress 2 (by
      intro i hi written
      apply entry.pendingFrame need _ ⟨i, hi, rfl⟩
      rcases written with stack | covered
      · exact .inl (callback_stack_in c s current.machine.data saved.stack _ stack)
      · exact .inr (.inl covered))
    rw [← read]
    exact pending need
  have amount : (512+preempt)+1-512 = preempt+1 := by
    rw [show (512+preempt)+1 = (preempt+1)+512 from by
      simp only [BitVec.add_assoc, BitVec.add_comm 512 preempt, BitVec.add_comm 512 1]]
    rw [BitVec.add_sub_cancel]
  have physical := LookupBh.enable_history fetch agree bh callback.machine.data (512+preempt)
    traced.ready.aligned traced.ready.mapped (load32_raw _ _ _ traced.ready.state.2)
    entry.bhHardirq (by rw [amount]; exact cbPending)
    (by
      intro a read written
      exact entry.bhStack a read (by
        have small := callback_stack_in c s callback.machine.data cbSaved.stack a written
        obtain ⟨i, hi, eq⟩ := small
        exact ⟨i, by omega, eq⟩))
    (by
      rw [amount]
      intro need a read written
      exact entry.pendingFrame need a read (.inl (callback_stack_in c s callback.machine.data cbSaved.stack a written)))
    0 [⟨callback.machine.data, Image.Lookup.entry+0x78⟩] [] rfl rfl
  have endpoint : Eventually (instructionStep fetch) (fun t =>
      Returned (LookupBh.called callback.machine.data) t (Image.Lookup.entry+0x89).toUInt64 ∧
      t.data.dmem.loadInt preemptCountAddress 4 = some (((512+preempt)-512).toNat : Int) ∧
      EqualOutside (fun a => InRange (callback.machine.data.regs.rsp.toBitVec-8) 8 a ∨
        InRange preemptCountAddress 4 a) callback.machine.data.dmem t.data.dmem)
      ⟨callback.machine.data, Image.Lookup.entry+0x78⟩ :=
    forget physical (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
  have bhRun := history_lift fetch _ _ endpoint callback.history
  have cursor : (⟨⟨callback.machine.data, Image.Lookup.entry+0x78⟩, callback.history⟩ : Executed) = callback := by rw [← callbackPC]
  rw [cursor] at bhRun
  apply eventually_trans (historyStep fetch) _ _ _ bhRun
  rintro afterBh ⟨ret, balanced, frame⟩
  have afterPC : afterBh.machine.pc = Image.Lookup.entry+0x89 := ret.1
  have afterSP : afterBh.machine.data.regs.rsp = callback.machine.data.regs.rsp := by
    rw [ret.2.1, (LookupBh.called_shape _).1]
    change callback.machine.data.regs.rsp-8+8 = callback.machine.data.regs.rsp
    exact UInt64.sub_add_cancel _ _
  have afterSaved := cbSaved.frame afterSP (by rw [ret.2.2.2.2.2.2.2]; rfl) _ frame (by
    intro a inside written
    rcases written with stack | count
    · apply outer_callback_apart s a inside
      simpa only [cbSaved.stack, UInt64.toBitVec_sub, BitVec.sub_sub,
        show (40 : UInt64).toBitVec+8 = (48 : BitVec 64) from rfl] using stack
    · exact entry.bhStack a count (outer_live c s a inside))
  have afterCoverage : LookupCoverageAt coverage preempt v afterBh.machine.data.dmem := by
    apply LookupCoverage.coverage_metadata_frame ⟨coverage, preempt, v⟩ _ _
      traced.ready.state.1 _ frame
    · intro a read written
      rcases written with stack | count
      · exact entry.serviceStack a (.inl read)
          (callback_stack_in c s callback.machine.data cbSaved.stack a stack)
      · exact entry.bhMetadata a (.inl read) count
    · intro needed
      apply Kcov.buffer_frame coverage _ _ (traced.ready.state.1.2.2.2 needed).2.2 _ frame
      intro a read written
      rcases written with stack | count
      · exact entry.serviceStack a (.inr (.inr ⟨needed, read⟩))
          (callback_stack_in c s callback.machine.data cbSaved.stack a stack)
      · exact entry.bhMetadata a (.inr ⟨needed, read⟩) count
  have afterCount : load32 afterBh.machine.data.dmem preemptCountAddress = some preempt := by
    unfold load32
    rw [balanced]
    have amount : (512+preempt)-512 = preempt := by
      rw [BitVec.add_comm, BitVec.add_sub_cancel]
    rw [amount]
    simp only [Option.map_some, BitVec.ofInt_natCast, BitVec.ofNat_toNat]
    rfl
  have returnRun := return_from_saved fetch agree s afterBh.machine.data ra afterSaved entry.frame.2 afterBh.history
  have cursor : (⟨⟨afterBh.machine.data, Image.Lookup.entry+0x89⟩, afterBh.history⟩ : Executed) = afterBh := by rw [← afterPC]
  rw [cursor] at returnRun
  apply eventually_weaken (historyStep fetch) _ _ _ _ (historySteps_eventually fetch 7 _ _ returnRun)
  rintro final ⟨returned, value, memory⟩
  have liftBh (q : MachineState)
      (localFrame : EqualOutside (fun a => InRange (callback.machine.data.regs.rsp.toBitVec-8) 8 a ∨
        InRange preemptCountAddress 4 a) callback.machine.data.dmem q.data.dmem) :
      EqualOutside (fun a => scanWrites current.machine.data ⟨coverage, preempt, v⟩ a ∨
        InRange preemptCountAddress 4 a) current.machine.data.dmem q.data.dmem := by
    intro a outside
    exact (traced.memory a (fun h => outside (.inl h))).trans (localFrame a (by
      rintro (stack | count)
      · apply outside (.inl (.inl _))
        simpa only [traced.stack] using stack
      · exact outside (.inr count)))
  have bhFrame := liftBh afterBh.machine frame
  refine ⟨returned, ?_, ?_, ?_, ?_⟩
  · rw [value, ret.2.2.1]
    exact cbBX
  · rw [memory]
    exact bhFrame
  · simpa only [memory] using afterCoverage
  · simpa only [memory] using afterCount

#print axioms common_finish
end Binary.Sequential
