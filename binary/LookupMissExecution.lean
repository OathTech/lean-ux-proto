import LookupClearFinish
import LookupCutFrames
import LookupMissSource

namespace Binary.LookupRelation
open Leanux Leanux.WG TrustBase LookupHistory LookupObservation
local instance : Labels := Image.linkedLabels

/-- Every no-owner lookup path, including arbitrary bucket collisions and
    first-match wrong-kind, from Pre to its actual ABI return. -/
theorem miss_execution (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (tracePc : TracePcContract fetch)
    (traceCmp : TraceCmp4Contract fetch) (traceConstCmp : TraceConstCmp4Contract fetch)
    (bh : BhEnableContract fetch)
    (c : Config) (coverage : KcovLayout) (preempt : BitVec 32) (ra : UInt64)
    (s : MachineData) (world : World)
    (pre : Pre_lookup c coverage preempt ra ⟨s, Image.Lookup.entry⟩ world)
    (focused : c.focus.owner = none)
    (answer : Option (IndexOwner × PeerId)) (finalWorld : World)
    (accepted : (indexLookup c.kinds c.query).run world = .ok (answer, finalWorld)) :
    Eventually (historyStep fetch) (fun final =>
      Returned ⟨s, Image.Lookup.entry⟩ final.machine ra ∧ final.machine.data.regs.rax = 0 ∧ answer = none ∧
      ∃ v points source,
        LookupEntry c coverage preempt ra ⟨s, Image.Lookup.entry⟩ world v ∧
        EqualOutside (LookupWrites c coverage preempt s v) s.dmem final.machine.data.dmem ∧
        ((MirrorHistory.lookup c.kinds c.query).run []).run world = .ok ((answer, source), finalWorld) ∧
        observe c.rxSection final.history = .ok points ∧
        MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection final.history) points source ∧
        ExecutedCorrespondence.CutsAligned (R c) c.rxSection final.history source ∧
        R c final.history points final.machine finalWorld ∧
        CutFrames (LookupWrites c coverage preempt s v) s.dmem final.history ∧
        LookupCoverageAt coverage preempt v final.machine.data.dmem ∧
        load32 final.machine.data.dmem preemptCountAddress = some preempt ∧
        (LookupPendingRead preempt → final.machine.data.dmem.loadInt softirqPendingAddress 2 = some 0) ∧
        EndsAtReturn (Image.Lookup.entry+0x94) final.history)
      ⟨⟨s, Image.Lookup.entry⟩, [⟨s, Image.Lookup.entry⟩]⟩ := by
  obtain ⟨v, entry⟩ := pre
  obtain ⟨answerEq, finalEq⟩ := lookup_no_owner_accepted c coverage preempt ra _ world v entry focused answer finalWorld accepted
  have sourceRun := lookup_no_owner_source c coverage preempt ra _ world v entry focused
  apply eventually_trans (historyStep fetch) _ _ _
    (start_from_entry fetch agree tracePc c coverage preempt ra s world v entry)
  intro started startedAt
  apply eventually_trans (historyStep fetch) _ _ _
    (header_from_started fetch agree c coverage preempt ra s world v entry started startedAt)
  intro head headAt
  apply eventually_trans (historyStep fetch) _ _ _
    (bucket_from_head fetch agree tracePc traceCmp traceConstCmp c coverage preempt ra s world v entry head headAt)
  intro bucket bucketAt
  have bucketCuts := bucket_cut_frames c coverage preempt s world v bucket bucketAt
  have saved := outer_saved_bucket c coverage preempt ra s world v entry bucket bucketAt
  have frame := bucket_write_frame c coverage preempt ra s world v entry bucket bucketAt
  obtain ⟨head, headAt, _, stop, bucketFrame, delta, observed, raw, matched, aligned, related, _, tags, _⟩ := bucketAt
  have places := selected_stop_none c v bucket.machine (entry.focus.1.trans focused) stop
  let seen := [entryPoint s] ++ delta
  let source := (LookupSearch.result c.kinds c.query v.bucket [sourceEntry world] world).1.2
  have latest : source.getLast?.map (·.world) = some finalWorld := by
    rw [finalEq]
    exact result_latest c v.bucket [sourceEntry world] world
  have projected : project c finalWorld = some v := by
    rw [finalEq, LookupSearch.result_world]
    exact entry.projected
  have sourceView : ∃ view, project c finalWorld = some view ∧ view.bucket = v.bucket := ⟨v, projected, rfl⟩
  have inactive : helperActive seen = false := by
    rw [helperActive_append_decisions _ _ tags]
    rfl
  have noReturn : lastHelperReturn seen = none := lastHelperReturn_append_decisions _ _ tags rfl
  have related' : R c bucket.history seen bucket.machine finalWorld := by simpa only [finalEq] using related
  have close (current : Executed) (pc : current.machine.pc = Image.Lookup.entry+0x71)
      (saved : OuterSaved s current.machine.data)
      (ready : LookupCoverage.CallsReady ⟨coverage, preempt, v⟩ (512+preempt) current.machine.data)
      (frame : EqualOutside (LookupWrites c coverage preempt s v) s.dmem current.machine.data.dmem)
      (related : R c current.history seen current.machine finalWorld)
      (observed : observe c.rxSection current.history = .ok seen)
      (matched : MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection current.history) seen source)
      (aligned : ExecutedCorrespondence.CutsAligned (R c) c.rxSection current.history source)
      (cutFrames : CutFrames (LookupWrites c coverage preempt s v) s.dmem current.history) :
      Eventually (historyStep fetch) (fun final =>
        Returned ⟨s, Image.Lookup.entry⟩ final.machine ra ∧ final.machine.data.regs.rax = 0 ∧ answer = none ∧
        ∃ v points source,
          LookupEntry c coverage preempt ra ⟨s, Image.Lookup.entry⟩ world v ∧
          EqualOutside (LookupWrites c coverage preempt s v) s.dmem final.machine.data.dmem ∧
          ((MirrorHistory.lookup c.kinds c.query).run []).run world = .ok ((answer, source), finalWorld) ∧
          observe c.rxSection final.history = .ok points ∧
          MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection final.history) points source ∧
          ExecutedCorrespondence.CutsAligned (R c) c.rxSection final.history source ∧
          R c final.history points final.machine finalWorld ∧
        CutFrames (LookupWrites c coverage preempt s v) s.dmem final.history ∧
        LookupCoverageAt coverage preempt v final.machine.data.dmem ∧
        load32 final.machine.data.dmem preemptCountAddress = some preempt ∧
        (LookupPendingRead preempt → final.machine.data.dmem.loadInt softirqPendingAddress 2 = some 0) ∧
        EndsAtReturn (Image.Lookup.entry+0x94) final.history) current := by
    have run := clear_finish fetch agree tracePc bh c coverage preempt ra s world v entry current pc finalWorld sourceView
      saved ready frame seen source related observed matched aligned latest inactive noReturn cutFrames
    apply eventually_weaken (historyStep fetch) _ _ _ _ run
    rintro final ⟨ret, zero, frame, full, matching, cuts, endpoint, frames, coverageAt, countAt, ended⟩
    refine ⟨ret, zero, answerEq, v, _, _, entry, frame, ?_, full, matching, cuts, endpoint, frames, coverageAt, countAt,
      pending_from_frame c coverage preempt ra s final.machine.data world v entry frame, ended⟩
    simpa only [answerEq, finalEq] using sourceRun
  rcases places with pc | pc
  · have scratch : ∀ view, project c finalWorld = some view → ∀ a, Reads c view a →
        ¬scanWrites bucket.machine.data ⟨coverage, preempt, v⟩ a := by
      intro view projection a read written
      have eq : view = v := Option.some.inj (projection.symm.trans projected)
      subst view
      apply entry.readsScratch a read
      rcases written with stack | covered
      · exact .inl (callback_stack_in c s bucket.machine.data saved.stack a stack)
      · exact .inr (.inl covered)
    have run := tail_callback fetch agree tracePc c finalWorld bucket 0x6c (.inl rfl) pc
      ⟨coverage, preempt, v⟩ (512+preempt) bucketFrame.ready seen delta source related' observed raw matched aligned latest
      inactive noReturn scratch
    apply eventually_trans (historyStep fetch) _ _ _ run
    rintro callback ⟨cbPC, _, _, traced, full, matching, cuts, endpoint⟩
    have cbSaved := saved.frame traced.frame.stack traced.frame.saved _ traced.frame.memory (by
      intro a inside written
      rcases written with stack | covered
      · apply outer_callback_apart s a inside
        simpa only [saved.stack, UInt64.toBitVec_sub, BitVec.sub_sub,
          show (40 : UInt64).toBitVec+8 = (48 : BitVec 64) from rfl] using stack
      · exact entry.coverageStack a covered (outer_live c s a inside))
    exact close callback (by simpa only [pc, show Image.Lookup.entry+0x6c+5 = Image.Lookup.entry+0x71 from rfl] using cbPC)
      cbSaved traced.frame.ready (lookup_frame_callback c coverage preempt s bucket.machine.data callback.machine.data v saved.stack frame traced.frame.memory)
      endpoint full matching cuts (by
        obtain ⟨tail, recorded, frames⟩ := traced.extension
        rw [recorded]
        apply bucketCuts.append_after frame (fun q member cut => (frames q member cut).memory)
        intro a written
        rcases written with stack | covered
        · exact .inl (callback_stack_in c s bucket.machine.data saved.stack a stack)
        · exact .inr (.inl covered))
  · exact close bucket pc saved bucketFrame.ready frame related' observed matched aligned bucketCuts

#print axioms miss_execution
end Binary.LookupRelation
