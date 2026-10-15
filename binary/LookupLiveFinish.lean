import LookupSelectedFrame

namespace Binary.LookupRelation
open Leanux Leanux.WG TrustBase LookupHistory LookupObservation
local instance : Labels := Image.linkedLabels

/-- Live tail including the out-parameter store, the common finish and
    preservation of its value through both remaining service calls. -/
theorem live_finish (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (tracePc : TracePcContract fetch) (bh : BhEnableContract fetch)
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
    (seen : List Point) (source : List MirrorHistory.Point)
    (related : R c current.history seen current.machine finalWorld)
    (observed : observe c.rxSection current.history = .ok seen)
    (matched : MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection current.history) seen source)
    (aligned : ExecutedCorrespondence.CutsAligned (R c) c.rxSection current.history source)
    (latest : source.getLast?.map (·.world) = some finalWorld)
    (inactive : helperActive seen = false) (noReturn : lastHelperReturn seen = none)
    (cutFrames : CutFrames (LookupWrites c coverage preempt s v) s.dmem current.history) :
    Eventually (historyStep fetch) (fun final =>
      Returned ⟨s, Image.Lookup.entry⟩ final.machine ra ∧
      final.machine.data.regs.rax = current.machine.data.regs.rbx ∧
      final.machine.data.dmem.loadInt s.regs.rcx.toBitVec 8 = some (current.machine.data.regs.rbp.toNat : Int) ∧
      EqualOutside (LookupWrites c coverage preempt s v) s.dmem final.machine.data.dmem ∧
      observe c.rxSection final.history = .ok (seen ++ [returned "wg_index_hashtable_lookup" final.machine]) ∧
      MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection final.history)
        (seen ++ [returned "wg_index_hashtable_lookup" final.machine]) (source ++ [⟨.returned "wg_index_hashtable_lookup", finalWorld⟩]) ∧
      ExecutedCorrespondence.CutsAligned (R c) c.rxSection final.history (source ++ [⟨.returned "wg_index_hashtable_lookup", finalWorld⟩]) ∧
      R c final.history (seen ++ [returned "wg_index_hashtable_lookup" final.machine]) final.machine finalWorld ∧
      CutFrames (LookupWrites c coverage preempt s v) s.dmem final.history ∧
      LookupCoverageAt coverage preempt v final.machine.data.dmem ∧
      load32 final.machine.data.dmem preemptCountAddress = some preempt ∧
      EndsAtReturn (Image.Lookup.entry+0x94) final.history) current := by
  obtain ⟨raw, rawObserved⟩ := observe_has_raw c.rxSection current.history seen observed
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
  have run := tail_callback fetch agree tracePc c finalWorld current 0xc5 (.inr (.inr rfl)) pc
    ⟨coverage, preempt, v⟩ (512+preempt) ready seen raw source related observed rawObserved matched aligned latest
    inactive noReturn scratch
  apply eventually_trans (historyStep fetch) _ _ _ run
  rintro callback ⟨cbPC, cbBX, cbBP, traced, full, matching, cuts, endpoint⟩
  have callbackPC : callback.machine.pc = Image.Lookup.entry+0xca := by
    simpa only [pc, show Image.Lookup.entry+0xc5+5 = Image.Lookup.entry+0xca from rfl] using cbPC
  have cbOutput : callback.machine.data.regs.r13 = s.regs.rcx := traced.frame.output.trans output
  have cbSaved := saved.frame traced.frame.stack traced.frame.saved _ traced.frame.memory (by
    intro a inside written
    rcases written with stack | covered
    · apply outer_callback_apart s a inside
      simpa only [saved.stack, UInt64.toBitVec_sub, BitVec.sub_sub,
        show (40 : UInt64).toBitVec+8 = (48 : BitVec 64) from rfl] using stack
    · exact entry.coverageStack a covered (outer_live c s a inside))
  have cbFrame := lookup_frame_callback c coverage preempt s current.machine.data callback.machine.data v saved.stack frame traced.frame.memory
  have cbCuts : CutFrames (LookupWrites c coverage preempt s v) s.dmem callback.history := by
    obtain ⟨tail, historyEq, frames⟩ := traced.extension
    rw [historyEq]
    exact cutFrames.append_after frame (fun q member cut => (frames q member cut).memory) (by
      intro a written
      rcases written with stack | covered
      · exact .inl (callback_stack_in c s current.machine.data saved.stack a stack)
      · exact .inr (.inl covered))
  have cbMapped : (callback.machine.data.dmem.loadInt callback.machine.data.regs.r13.toBitVec 8).isSome = true := by
    rw [cbOutput]
    have read := traced.frame.memory.loadInt s.regs.rcx.toBitVec 8 (by
      intro i hi written
      exact outputScratch current.machine.data saved.stack _ ⟨i, hi, rfl⟩ (.inl written))
    rw [← read]
    exact mapped
  have storedRun := output_simulation fetch agree c finalWorld callback.machine.data callback.history seen source
    (by simpa only [← callbackPC] using endpoint) full matching cuts latest inactive noReturn cbMapped (by
      intro view projected a read written
      exact entry.outputProtected a ⟨needed, by simpa only [cbOutput] using written⟩ (.inl (readBack view projected a read)))
  have cursor : (⟨⟨callback.machine.data, Image.Lookup.entry+0xca⟩, callback.history⟩ : Executed) = callback := by rw [← callbackPC]
  rw [cursor] at storedRun
  apply eventually_trans (historyStep fetch) _ _ _ (historySteps_eventually fetch 2 _ _ storedRun)
  rintro stored ⟨machine, recorded, full, matching, cuts, endpoint⟩
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
  have storedCuts : CutFrames (LookupWrites c coverage preempt s v) s.dmem stored.history := by
    rw [recorded]
    intro q member cut
    rcases List.mem_append.mp member with old | new
    · exact cbCuts q old cut
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at new
      rcases new with eq | eq
      · subst q
        change EqualOutside (LookupWrites c coverage preempt s v) s.dmem (outputStored callback.machine.data).dmem
        simpa only [machine] using storedFrame
      · subst q
        exact storedFrame
  have storedState := LookupCoverage.state_frame ⟨coverage, preempt, v⟩ (512+preempt) _ _ traced.frame.ready.state _ storeFrame (by
    intro a read written
    exact entry.outputProtected a ⟨needed, written⟩ (.inr (.inl read)))
  have storedReady := ready_at_outer c coverage preempt ra s stored.machine.data world v entry storedSaved.stack storedState (by
    rw [machine]
    exact storeInt_defined _ _ _ _ _ _ traced.frame.ready.mapped)
  have finish := common_finish fetch agree tracePc bh c coverage preempt ra s world v entry stored (by rw [machine])
    finalWorld sourceView storedSaved storedReady (pending_from_frame c coverage preempt ra s stored.machine.data world v entry storedFrame)
    seen source endpoint full matching cuts latest inactive noReturn
  apply eventually_weaken (historyStep fetch) _ _ _ _ finish
  rintro final ⟨ret, value, finalFrame, full, matching, cuts, endpoint, coverageAt, countAt, ended, suffix, finalHistory, suffixFrames⟩
  refine ⟨ret, ?_, ?_, ?_, full, matching, cuts, endpoint, ?_, coverageAt, countAt, ended⟩
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
  · rw [finalHistory]
    exact storedCuts.append_after storedFrame suffixFrames (by
      intro a written
      rcases written with (slot | covered) | count
      · exact .inl (callback_stack_in c s stored.machine.data storedSaved.stack a slot)
      · exact .inr (.inl covered)
      · exact .inr (.inr (.inl count)))

#print axioms live_finish
end Binary.LookupRelation
