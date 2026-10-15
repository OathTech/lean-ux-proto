import LookupWriteFrame

namespace Binary.LookupRelation
open Leanux Leanux.WG TrustBase LookupHistory LookupObservation
local instance : Labels := Image.linkedLabels

/-- Shared NULL/dead/miss finish from the actual XOR site. -/
theorem clear_finish (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (tracePc : TracePcContract fetch) (bh : BhEnableContract fetch)
    (c : Config) (coverage : KcovLayout) (preempt : BitVec 32) (ra : UInt64)
    (s : MachineData) (world : World) (v : View)
    (entry : LookupEntry c coverage preempt ra ⟨s, Image.Lookup.entry⟩ world v)
    (current : Executed) (pc : current.machine.pc = Image.Lookup.entry+0x71)
    (finalWorld : World) (sourceView : ∃ view, project c finalWorld = some view ∧ view.bucket = v.bucket)
    (saved : OuterSaved s current.machine.data)
    (ready : LookupCoverage.CallsReady ⟨coverage, preempt, v⟩ (512+preempt) current.machine.data)
    (frame : EqualOutside (LookupWrites c coverage preempt s v) s.dmem current.machine.data.dmem)
    (seen : List Point) (source : List MirrorHistory.Point)
    (related : R c current.history seen current.machine finalWorld)
    (observed : observe c.rxSection current.history = .ok seen)
    (matched : MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection current.history) seen source)
    (aligned : ExecutedCorrespondence.CutsAligned (R c) c.rxSection current.history source)
    (latest : source.getLast?.map (·.world) = some finalWorld)
    (inactive : helperActive seen = false) (noReturn : lastHelperReturn seen = none)
    (cutFrames : CutFrames (LookupWrites c coverage preempt s v) s.dmem current.history) :
    Eventually (historyStep fetch) (fun final =>
      Returned ⟨s, Image.Lookup.entry⟩ final.machine ra ∧ final.machine.data.regs.rax = 0 ∧
      EqualOutside (LookupWrites c coverage preempt s v) s.dmem final.machine.data.dmem ∧
      observe c.rxSection final.history = .ok (seen ++ [returned "wg_index_hashtable_lookup" final.machine]) ∧
      MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection final.history)
        (seen ++ [returned "wg_index_hashtable_lookup" final.machine]) (source ++ [⟨.returned "wg_index_hashtable_lookup", finalWorld⟩]) ∧
      ExecutedCorrespondence.CutsAligned (R c) c.rxSection final.history (source ++ [⟨.returned "wg_index_hashtable_lookup", finalWorld⟩]) ∧
      R c final.history (seen ++ [returned "wg_index_hashtable_lookup" final.machine]) final.machine finalWorld ∧
      CutFrames (LookupWrites c coverage preempt s v) s.dmem final.history) current := by
  have run := clear_simulation fetch agree c finalWorld current.machine.data current.history seen source
    (by simpa only [← pc] using related) observed matched aligned latest inactive noReturn
  have cursor : (⟨⟨current.machine.data, Image.Lookup.entry+0x71⟩, current.history⟩ : Executed) = current := by rw [← pc]
  rw [cursor] at run
  apply eventually_trans (historyStep fetch) _ _ _ (historySteps_eventually fetch 1 _ _ run)
  rintro cleared ⟨af, machine, recorded, full, matching, cuts, endpoint⟩
  have clearPC : cleared.machine.pc = Image.Lookup.entry+0x73 := by rw [machine]
  have sameMemory : cleared.machine.data.dmem = current.machine.data.dmem := by rw [machine]; rfl
  have sameStack : cleared.machine.data.regs.rsp = current.machine.data.regs.rsp := by rw [machine, (PeerGet.zeroed_shape _ _).1]
  have clearSaved : OuterSaved s cleared.machine.data :=
    ⟨sameStack.trans saved.stack, by rw [machine, (PeerGet.zeroed_shape _ _).1]; exact saved.saved,
      by simpa only [sameMemory] using saved.memory⟩
  have clearFrame : EqualOutside (LookupWrites c coverage preempt s v) s.dmem cleared.machine.data.dmem := by
    simpa only [sameMemory] using frame
  have clearCuts : CutFrames (LookupWrites c coverage preempt s v) s.dmem cleared.history := by
    rw [recorded]
    intro q member cut
    rcases List.mem_append.mp member with old | new
    · exact cutFrames q old cut
    · have eq : q = cleared.machine := List.mem_singleton.mp new
      simpa only [eq] using clearFrame
  have finish := common_finish fetch agree tracePc bh c coverage preempt ra s world v entry cleared clearPC
    finalWorld sourceView clearSaved (ready.congr sameMemory sameStack)
    (pending_from_frame c coverage preempt ra s cleared.machine.data world v entry clearFrame)
    seen source endpoint full matching cuts latest inactive noReturn
  apply eventually_weaken (historyStep fetch) _ _ _ _ finish
  rintro final ⟨ret, value, memory, full, matching, cuts, endpoint, suffix, finalHistory, suffixFrames⟩
  refine ⟨ret, ?_, ?_, full, matching, cuts, endpoint, ?_⟩
  · rw [value, machine, (PeerGet.zeroed_shape _ _).1]
  · intro a outside
    exact (clearFrame a outside).trans (memory a (by
      rintro ((stack | covered) | count)
      · exact outside (.inl (callback_stack_in c s cleared.machine.data clearSaved.stack a stack))
      · exact outside (.inr (.inl covered))
      · exact outside (.inr (.inr (.inl count)))))
  · rw [finalHistory]
    exact clearCuts.append_after clearFrame suffixFrames (by
      intro a written
      rcases written with (stack | covered) | count
      · exact .inl (callback_stack_in c s cleared.machine.data clearSaved.stack a stack)
      · exact .inr (.inl covered)
      · exact .inr (.inr (.inl count)))

#print axioms clear_finish
end Binary.LookupRelation
