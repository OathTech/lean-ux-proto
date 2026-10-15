import CutFrames
import LookupBhSimulation
import LookupOuterPrepared

namespace Binary.LookupRelation
open Leanux Leanux.WG TrustBase LookupHistory LookupObservation
local instance : Labels := Image.linkedLabels

theorem observe_has_raw (rx : Nat) (history : List MachineState) (seen : List Point)
    (observed : observe rx history = .ok seen) :
    ∃ raw, observeHistory (edge rx) history = .ok raw := by
  cases history with
  | nil => cases observed
  | cons initial rest =>
    by_cases pc : initial.pc = Image.Lookup.entry
    · cases raw : observeHistory (edge rx) (initial :: rest) with
      | error e => simp [observe, pc, raw] at observed; cases observed
      | ok points => exact ⟨points, rfl⟩
    · simp [observe, pc] at observed; cases observed

theorem callback_stack_in (c : Config) (s t : MachineData)
    (stack : t.regs.rsp = s.regs.rsp-40) (a : Address)
    (inside : InRange (t.regs.rsp.toBitVec-8) 8 a) : LookupStackWrites c ⟨s, Image.Lookup.entry⟩ a := by
  have words : 6 ≤ LookupStackWords c := by unfold LookupStackWords; split <;> decide
  have loc : t.regs.rsp.toBitVec-8 = s.regs.rsp.toBitVec-48 := by
    rw [stack, UInt64.toBitVec_sub, BitVec.sub_sub]; rfl
  obtain ⟨i, hi, eq⟩ := inside
  exact backwards_range s.regs.rsp.toBitVec 48 (8*LookupStackWords c) 0 (by omega) a
    ⟨i, by omega, by simpa only [loc, show BitVec.ofNat 64 48 = (48 : BitVec 64) from rfl] using eq⟩

/-- Common finish from +73 through the actual callback, BH-enable and ABI
    return. All footprint separation comes from the original entry. The
    saved frame and pending word are intermediate proved invariants. -/
theorem common_finish (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (tracePc : TracePcContract fetch) (bh : BhEnableContract fetch)
    (c : Config) (coverage : KcovLayout) (preempt : BitVec 32) (ra : UInt64)
    (s : MachineData) (world : World) (v : View)
    (entry : LookupEntry c coverage preempt ra ⟨s, Image.Lookup.entry⟩ world v)
    (current : Executed) (pc : current.machine.pc = Image.Lookup.entry+0x73)
    (finalWorld : World) (sourceView : ∃ view, project c finalWorld = some view ∧ view.bucket = v.bucket)
    (saved : OuterSaved s current.machine.data)
    (ready : LookupCoverage.CallsReady ⟨coverage, preempt, v⟩ (512+preempt) current.machine.data)
    (pending : LookupPendingRead preempt → current.machine.data.dmem.loadInt softirqPendingAddress 2 = some 0)
    (seen : List Point) (source : List MirrorHistory.Point)
    (related : R c current.history seen current.machine finalWorld)
    (observed : observe c.rxSection current.history = .ok seen)
    (matched : MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection current.history) seen source)
    (aligned : ExecutedCorrespondence.CutsAligned (R c) c.rxSection current.history source)
    (latest : source.getLast?.map (·.world) = some finalWorld)
    (inactive : helperActive seen = false) (noReturn : lastHelperReturn seen = none) :
    Eventually (historyStep fetch) (fun final =>
      Returned ⟨s, Image.Lookup.entry⟩ final.machine ra ∧
      final.machine.data.regs.rax = current.machine.data.regs.rbx ∧
      EqualOutside (fun a => scanWrites current.machine.data ⟨coverage, preempt, v⟩ a ∨
        InRange preemptCountAddress 4 a) current.machine.data.dmem final.machine.data.dmem ∧
      observe c.rxSection final.history = .ok (seen ++ [returned "wg_index_hashtable_lookup" final.machine]) ∧
      MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection final.history)
        (seen ++ [returned "wg_index_hashtable_lookup" final.machine]) (source ++ [⟨.returned "wg_index_hashtable_lookup", finalWorld⟩]) ∧
      ExecutedCorrespondence.CutsAligned (R c) c.rxSection final.history (source ++ [⟨.returned "wg_index_hashtable_lookup", finalWorld⟩]) ∧
      R c final.history (seen ++ [returned "wg_index_hashtable_lookup" final.machine]) final.machine finalWorld ∧
      EndsAtReturn (Image.Lookup.entry+0x94) final.history ∧
      ∃ suffix, final.history = current.history ++ suffix ∧
        CutFrames (fun a => scanWrites current.machine.data ⟨coverage, preempt, v⟩ a ∨
          InRange preemptCountAddress 4 a) current.machine.data.dmem suffix) current := by
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
  have run := tail_callback fetch agree tracePc c finalWorld current 0x73 (.inr (.inl rfl)) pc
    ⟨coverage, preempt, v⟩ (512+preempt) ready seen raw source related observed rawObserved matched aligned latest
    inactive noReturn scratch
  apply eventually_trans (historyStep fetch) _ _ _ run
  rintro callback ⟨cbPC, cbBX, cbBP, traced, full, matching, cuts, endpoint⟩
  obtain ⟨cbTail, cbHistory, cbCuts⟩ := traced.extension
  have callbackPC : callback.machine.pc = Image.Lookup.entry+0x78 := by simpa only [pc, show Image.Lookup.entry+0x73+5 = Image.Lookup.entry+0x78 from rfl] using cbPC
  have cbSaved := saved.frame traced.frame.stack traced.frame.saved _ traced.frame.memory (by
    intro a inside written
    rcases written with stack | covered
    · apply outer_callback_apart s a inside
      simpa only [saved.stack, UInt64.toBitVec_sub, BitVec.sub_sub,
        show (40 : UInt64).toBitVec+8 = (48 : BitVec 64) from rfl] using stack
    · exact entry.coverageStack a covered (outer_live c s a inside))
  have cbPending : LookupPendingRead preempt → callback.machine.data.dmem.loadInt softirqPendingAddress 2 = some 0 := by
    intro need
    have read := traced.frame.memory.loadInt softirqPendingAddress 2 (by
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
  have bhRun := bh_simulation fetch agree bh c finalWorld callback.machine.data (512+preempt)
    traced.frame.ready.aligned traced.frame.ready.mapped (load32_raw _ _ _ traced.frame.ready.state.2)
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
    callback.history raw seen source traced.observed (by simpa only [← callbackPC] using endpoint)
    full matching cuts latest inactive noReturn (by
      intro view projected a read written
      apply entry.readsScratch a (readBack view projected a read)
      rcases written with stack | count
      · exact .inl (callback_stack_in c s callback.machine.data cbSaved.stack a stack)
      · exact .inr (.inr count))
  have cursor : (⟨⟨callback.machine.data, Image.Lookup.entry+0x78⟩, callback.history⟩ : Executed) = callback := by rw [← callbackPC]
  rw [cursor] at bhRun
  apply eventually_trans (historyStep fetch) _ _ _ bhRun
  rintro afterBh ⟨ret, balanced, frame, full, matching, cuts, endpoint, bhTail, bhHistory, bhCuts⟩
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
  have returnRun := return_from_saved fetch agree c finalWorld s afterBh.machine.data ra afterSaved entry.frame.2
    afterBh.history seen source (by simpa only [← afterPC] using endpoint) full matching cuts latest inactive noReturn
  have cursor : (⟨⟨afterBh.machine.data, Image.Lookup.entry+0x89⟩, afterBh.history⟩ : Executed) = afterBh := by rw [← afterPC]
  rw [cursor] at returnRun
  apply eventually_weaken (historyStep fetch) _ _ _ _ (historySteps_eventually fetch 7 _ _ returnRun)
  rintro final ⟨returned, value, memory, full, matching, cuts, endpoint, ended, retTail, retHistory, retMem⟩
  have liftBh (q : MachineState)
      (localFrame : EqualOutside (fun a => InRange (callback.machine.data.regs.rsp.toBitVec-8) 8 a ∨
        InRange preemptCountAddress 4 a) callback.machine.data.dmem q.data.dmem) :
      EqualOutside (fun a => scanWrites current.machine.data ⟨coverage, preempt, v⟩ a ∨
        InRange preemptCountAddress 4 a) current.machine.data.dmem q.data.dmem := by
    intro a outside
    exact (traced.frame.memory a (fun h => outside (.inl h))).trans (localFrame a (by
      rintro (stack | count)
      · apply outside (.inl (.inl _))
        simpa only [traced.frame.stack] using stack
      · exact outside (.inr count)))
  have bhFrame := liftBh afterBh.machine frame
  refine ⟨returned, ?_, ?_, full, matching, cuts, endpoint, ended, (cbTail ++ bhTail) ++ retTail, ?_, ?_⟩
  · rw [value, ret.2.2.1]
    exact cbBX
  · rw [memory]
    exact bhFrame
  · simp only [retHistory, bhHistory, cbHistory, List.append_assoc]
  · intro q member cut
    rcases List.mem_append.mp member with earlier | last
    · rcases List.mem_append.mp earlier with callback | bh
      · intro a outside
        exact (cbCuts q callback cut).memory a (fun h => outside (.inl h))
      · exact liftBh q (bhCuts q bh cut)
    · rw [retMem q last]
      exact bhFrame

#print axioms observe_has_raw
#print axioms callback_stack_in
#print axioms common_finish
end Binary.LookupRelation
