import SequentialTails
import SequentialFirstFinish
namespace Binary.Sequential.First
open Leanux Leanux.WG TrustBase LookupRelation LookupHistory LookupObservation Callback
local instance : Labels := Image.linkedLabels
theorem clear_finish (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (tracePc : LeafService fetch (.ofNat 0xffffffff810f31f0) (KcovReady .pc) (KcovWrites .pc) (KcovEffect .pc)) (bh : LeafService fetch (.ofNat 0xffffffff810732c0) BhEnableReady (fun _ => InRange preemptCountAddress 4) (fun before after => ∀ old : BitVec 32, before.data.dmem.loadInt preemptCountAddress 4 = some (old.toNat : Int) → after.data.dmem.loadInt preemptCountAddress 4 = some ((old-before.data.regs.get (.low .rsi .W32)).toNat : Int)))
    (c : Config) (coverage : KcovLayout) (preempt : BitVec 32) (ra : UInt64)
    (s : MachineData) (world : World) (v : View)
    (entry : LookupEntry c coverage preempt ra ⟨s, Image.Lookup.entry⟩ world v)
    (current : Executed) (pc : current.machine.pc = Image.Lookup.entry+0x71)
    (finalWorld : World) (sourceView : ∃ view, project c finalWorld = some view ∧ view.bucket = v.bucket)
    (saved : OuterSaved s current.machine.data)
    (ready : LookupCoverage.CallsReady ⟨coverage, preempt, v⟩ (512+preempt) current.machine.data)
    (frame : EqualOutside (LookupWrites c coverage preempt s v) s.dmem current.machine.data.dmem)
    (related : Related c current.machine finalWorld) :
    Eventually (guardedHistoryStep fetch (StackGuard s.regs.rsp)) (fun final =>
      Returned ⟨s, Image.Lookup.entry⟩ final.machine ra ∧ final.machine.data.regs.rax = 0 ∧
      EqualOutside (LookupWrites c coverage preempt s v) s.dmem final.machine.data.dmem ∧
      Related c final.machine finalWorld ∧
      LookupCoverageAt coverage preempt v final.machine.data.dmem ∧
      load32 final.machine.data.dmem preemptCountAddress = some preempt) current := by
  have run := PeerGet.xor32_history fetch (Image.Lookup.entry+0x71) 2 (.low .rbx .W32) (by decide)
    (agree _ _ (by rfl)) current.machine.data [⟨current.machine.data,Image.Lookup.entry+0x71⟩]
  have guarded := history_guard_suffix (guard := StackGuard s.regs.rsp)
    (historySteps_eventually fetch 1 _ _ run) rfl (by
      rintro t ⟨af,machine,recorded⟩
      refine ⟨_,recorded,?_⟩
      intro q member
      simp only [List.dropLast_cons_cons,List.dropLast_singleton,List.mem_singleton] at member
      subst q
      change current.machine.data.regs.rsp≠s.regs.rsp+8
      rw [saved.stack]; stack_not_return)
  have endpoint := guarded_forget (Q := fun t => ∃ af,t=⟨PeerGet.zeroed current.machine.data (.low .rbx .W32) af,Image.Lookup.entry+0x73⟩)
    guarded (fun _ h => ⟨h.choose,h.choose_spec.1⟩)
  have lifted := guarded_lift endpoint current.history
  have cursor : (⟨⟨current.machine.data, Image.Lookup.entry+0x71⟩, current.history⟩ : Executed) = current := by rw [←pc]
  rw [cursor] at lifted
  apply eventually_trans (guardedHistoryStep fetch (StackGuard s.regs.rsp)) _ _ _ lifted
  rintro cleared ⟨af,machine⟩
  have clearPC : cleared.machine.pc = Image.Lookup.entry+0x73 := by rw [machine]
  have sameMemory : cleared.machine.data.dmem = current.machine.data.dmem := by rw [machine]; rfl
  have sameStack : cleared.machine.data.regs.rsp = current.machine.data.regs.rsp := by rw [machine, (PeerGet.zeroed_shape _ _).1]
  have clearSaved : OuterSaved s cleared.machine.data :=
    ⟨sameStack.trans saved.stack, by rw [machine, (PeerGet.zeroed_shape _ _).1]; exact saved.saved,
      by simpa only [sameMemory] using saved.memory⟩
  have clearFrame : EqualOutside (LookupWrites c coverage preempt s v) s.dmem cleared.machine.data.dmem := by
    simpa only [sameMemory] using frame
  have clearRelated : Related c cleared.machine finalWorld := by
    obtain ⟨view, projected, physical⟩ := related
    exact ⟨view, projected, by simpa only [sameMemory] using physical⟩
  have finish := common_finish fetch agree tracePc bh c coverage preempt ra s world v entry cleared clearPC
    clearSaved (ready.congr sameMemory sameStack)
    (pending_from_frame c coverage preempt ra s cleared.machine.data world v entry clearFrame)
  apply eventually_weaken (guardedHistoryStep fetch (StackGuard s.regs.rsp)) _ _ _ _ finish
  rintro final ⟨ret, value, memory, coverageAt, countAt⟩
  refine ⟨ret, ?_, ?_, ?_, coverageAt, countAt⟩
  · rw [value, machine, (PeerGet.zeroed_shape _ _).1]
  · intro a outside
    exact (clearFrame a outside).trans (memory a (by
      rintro ((stack | covered) | count)
      · exact outside (.inl (callback_stack_in c s cleared.machine.data clearSaved.stack a stack))
      · exact outside (.inr (.inl covered))
      · exact outside (.inr (.inr (.inl count)))))
  · exact finish_related c coverage preempt ra s world v entry cleared final clearSaved.stack
      finalWorld sourceView clearRelated memory

theorem live_finish (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (tracePc : LeafService fetch (.ofNat 0xffffffff810f31f0) (KcovReady .pc) (KcovWrites .pc) (KcovEffect .pc)) (bh : LeafService fetch (.ofNat 0xffffffff810732c0) BhEnableReady (fun _ => InRange preemptCountAddress 4) (fun before after => ∀ old : BitVec 32, before.data.dmem.loadInt preemptCountAddress 4 = some (old.toNat : Int) → after.data.dmem.loadInt preemptCountAddress 4 = some ((old-before.data.regs.get (.low .rsi .W32)).toNat : Int)))
    (c : Config) (coverage : KcovLayout) (preempt : BitVec 32) (ra : UInt64)
    (s : MachineData) (world : World) (v : View)
    (entry : LookupEntry c coverage preempt ra ⟨s, Image.Lookup.entry⟩ world v)
    (current : Executed) (pc : current.machine.pc = Image.Lookup.entry+0xc5)
    (finalWorld : World) (sourceView : ∃ view, project c finalWorld = some view ∧ view.bucket = v.bucket)
    (saved : OuterSaved s current.machine.data)
    (ready : LookupCoverage.CallsReady ⟨coverage, preempt, v⟩ (512+preempt) current.machine.data)
    (frame : EqualOutside (LookupWrites c coverage preempt s v) s.dmem current.machine.data.dmem)
    (output : current.machine.data.regs.r13 = s.regs.rcx)
    (needed : LookupOutputNeeded v)
    (mapped : (current.machine.data.dmem.loadInt s.regs.rcx.toBitVec 8).isSome = true)
    (related : Related c current.machine finalWorld) :
    Eventually (guardedHistoryStep fetch (StackGuard s.regs.rsp)) (fun final =>
      Returned ⟨s, Image.Lookup.entry⟩ final.machine ra ∧
      final.machine.data.regs.rax = current.machine.data.regs.rbx ∧
      final.machine.data.dmem.loadInt s.regs.rcx.toBitVec 8 = some (current.machine.data.regs.rbp.toNat : Int) ∧
      EqualOutside (LookupWrites c coverage preempt s v) s.dmem final.machine.data.dmem ∧
      Related c final.machine finalWorld ∧
      LookupCoverageAt coverage preempt v final.machine.data.dmem ∧
      load32 final.machine.data.dmem preemptCountAddress = some preempt) current := by
  have readBack : ∀ view, project c finalWorld = some view → ∀ a, Reads c view a → Reads c v a := by
    obtain ⟨finalView, projected, sameBucket⟩ := sourceView
    intro view projected' a read
    have eq : view = finalView := Option.some.inj (projected'.symm.trans projected)
    simpa only [eq, Reads, sameBucket] using read
  have scratch : ∀ view, project c finalWorld = some view → ∀ a, Reads c view a →
      ¬scanWrites current.machine.data ⟨coverage, preempt, v⟩ a := by
    intro view projected a read written
    apply entry.readsScratch a (readBack view projected a read)
    rcases written with stack | covered
    · exact .inl (callback_stack_in c s current.machine.data saved.stack a stack)
    · exact .inr (.inl covered)
  have outputScratch (t : MachineData) (sp : t.regs.rsp = s.regs.rsp-40) (a : Address)
      (inside : InRange s.regs.rcx.toBitVec 8 a) :
      ¬(scanWrites t ⟨coverage, preempt, v⟩ a ∨ InRange preemptCountAddress 4 a) := by
    intro written
    apply entry.outputProtected a ⟨needed, inside⟩
    rcases written with (slot | covered) | count
    · apply Or.inr (Or.inr (Or.inl _))
      have loc : t.regs.rsp.toBitVec-8 = s.regs.rsp.toBitVec-48 := by
        rw [sp, UInt64.toBitVec_sub, BitVec.sub_sub]; rfl
      obtain ⟨i, hi, eq⟩ := slot
      exact ⟨i, by omega, by simpa only [loc] using eq⟩
    · exact .inr (.inr (.inr covered))
    · exact .inr (.inl (.inr (.inl count)))
  have run := callback (outer := s.regs.rsp) fetch agree tracePc current 0xc5 (.inr (.inr rfl)) pc
    ⟨coverage, preempt, v⟩ (512+preempt) (by rw [saved.stack]; constructor <;> stack_not_return) ready
  apply eventually_trans (guardedHistoryStep fetch (StackGuard s.regs.rsp)) _ _ _ run
  rintro callback ⟨cbPC, cbBX, cbBP, traced⟩
  have callbackPC : callback.machine.pc = Image.Lookup.entry+0xca := by
    simpa only [pc, show Image.Lookup.entry+0xc5+5 = Image.Lookup.entry+0xca from rfl] using cbPC
  have cbOutput : callback.machine.data.regs.r13 = s.regs.rcx := traced.output.trans output
  have cbSaved := saved.frame traced.stack traced.saved _ traced.memory (by
    intro a inside written
    rcases written with stack | covered
    · apply outer_callback_apart s a inside
      simpa only [saved.stack, UInt64.toBitVec_sub, BitVec.sub_sub,
        show (40 : UInt64).toBitVec+8 = (48 : BitVec 64) from rfl] using stack
    · exact entry.coverageStack a covered (outer_live c s a inside))
  have cbFrame := lookup_frame_callback c coverage preempt s current.machine.data callback.machine.data v saved.stack frame traced.memory
  have cbRelated : Related c callback.machine finalWorld := related.frame traced.memory scratch
  have cbMapped : (callback.machine.data.dmem.loadInt callback.machine.data.regs.r13.toBitVec 8).isSome = true := by
    rw [cbOutput]
    have read := traced.memory.loadInt s.regs.rcx.toBitVec 8 (by
      intro i hi written
      exact outputScratch current.machine.data saved.stack _ ⟨i, hi, rfl⟩ (.inl written))
    rw [← read]
    exact mapped
  have storedRun := output_history fetch agree callback.machine.data cbMapped [⟨callback.machine.data,Image.Lookup.entry+0xca⟩]
  have guarded := history_guard_suffix (guard := StackGuard s.regs.rsp)
    (historySteps_eventually fetch 2 _ _ storedRun) rfl (by
      rintro t ⟨machine,recorded⟩
      refine ⟨_,recorded,?_⟩
      intro q member
      simp only [List.dropLast_cons_cons,List.dropLast_singleton,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      all_goals change callback.machine.data.regs.rsp≠s.regs.rsp+8
      all_goals rw [cbSaved.stack]; stack_not_return)
  have endpoint := guarded_forget (Q := fun t => t=⟨outputStored callback.machine.data,Image.Lookup.entry+0x73⟩) guarded (fun _ h => h.1)
  have lifted := guarded_lift endpoint callback.history
  have cursor : (⟨⟨callback.machine.data,Image.Lookup.entry+0xca⟩,callback.history⟩ : Executed)=callback := by rw [←callbackPC]
  rw [cursor] at lifted
  apply eventually_trans (guardedHistoryStep fetch (StackGuard s.regs.rsp)) _ _ _ lifted
  intro stored machine
  have storeFrame : EqualOutside (InRange s.regs.rcx.toBitVec 8) callback.machine.data.dmem stored.machine.data.dmem := by
    rw [machine, ← cbOutput]
    exact output_frame _
  have storedSaved := cbSaved.frame (by rw [machine]; rfl) (by rw [machine]; rfl) _ storeFrame (by
    intro a inside written
    apply entry.outputProtected a ⟨needed, written⟩
    apply Or.inr (Or.inr (Or.inl _))
    have base : s.regs.rsp.toBitVec-40 = s.regs.rsp.toBitVec-48+8 := by
      rw [show (48 : BitVec 64) = 40+8 from rfl, ← BitVec.sub_sub, BitVec.sub_add_cancel]
    obtain ⟨i, hi, eq⟩ := inside
    refine ⟨8+i, by omega, ?_⟩
    simpa only [base, BitVec.ofNat_add, BitVec.add_assoc, show BitVec.ofNat 64 8 = (8 : BitVec 64) from rfl] using eq)
  have storedFrame : EqualOutside (LookupWrites c coverage preempt s v) s.dmem stored.machine.data.dmem := by
    intro a outside
    exact (cbFrame a outside).trans (storeFrame a (fun h => outside (.inr (.inr (.inr (.inr ⟨needed, h⟩))))))
  have storedRelated : Related c stored.machine finalWorld := cbRelated.frame storeFrame (by
    intro view projected a read written
    exact entry.outputProtected a ⟨needed, written⟩ (.inl (readBack view projected a read)))
  have storedState := LookupCoverage.state_frame ⟨coverage, preempt, v⟩ (512+preempt) _ _ traced.ready.state _ storeFrame (by
    intro a read written
    exact entry.outputProtected a ⟨needed, written⟩ (.inr (.inl read)))
  have storedReady := ready_at_outer c coverage preempt ra s stored.machine.data world v entry storedSaved.stack storedState (by
    rw [machine]
    exact storeInt_defined _ _ _ _ _ _ traced.ready.mapped)
  have finish := common_finish fetch agree tracePc bh c coverage preempt ra s world v entry stored (by rw [machine])
    storedSaved storedReady (pending_from_frame c coverage preempt ra s stored.machine.data world v entry storedFrame)
  apply eventually_weaken (guardedHistoryStep fetch (StackGuard s.regs.rsp)) _ _ _ _ finish
  rintro final ⟨ret, value, finalFrame, coverageAt, countAt⟩
  refine ⟨ret, ?_, ?_, ?_, ?_, coverageAt, countAt⟩
  · rw [value, machine]
    exact cbBX
  · have read := finalFrame.loadInt s.regs.rcx.toBitVec 8 (by
      intro i hi
      exact outputScratch stored.machine.data storedSaved.stack _ ⟨i, hi, rfl⟩)
    rw [← read, machine, ← cbOutput, output_value, cbBP]
  · intro a outside
    exact (storedFrame a outside).trans (finalFrame a (by
      rintro ((slot | covered) | count)
      · exact outside (.inl (callback_stack_in c s stored.machine.data storedSaved.stack a slot))
      · exact outside (.inr (.inl covered))
      · exact outside (.inr (.inr (.inl count)))))
  · exact finish_related c coverage preempt ra s world v entry stored final storedSaved.stack
      finalWorld sourceView storedRelated finalFrame

#print axioms clear_finish
#print axioms live_finish
end Binary.Sequential.First
