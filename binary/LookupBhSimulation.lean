import LookupSilentTail
import LookupBhHistory

namespace Binary.LookupRelation
open Leanux Leanux.WG TrustBase LookupHistory LookupObservation
local instance : Labels := Image.linkedLabels

/-- Execute the BH argument setup, CALL and named no-work service, keeping
    the exact accepted source prefix and R at each actual anchored cut. -/
theorem bh_simulation (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (contract : BhEnableContract fetch)
    (c : Config) (world : World)
    (s : MachineData) (count : BitVec 32)
    (aligned : s.regs.rsp.toNat % 8 = 0)
    (mapped : (s.dmem.loadInt (s.regs.rsp.toBitVec-8) 8).isSome = true)
    (preempt : s.dmem.loadInt preemptCountAddress 4 = some (count.toNat : Int))
    (hardirq : count &&& 0x000f0000 = 0)
    (pending : (count+1-512) &&& 0x00ffff00 = 0 → s.dmem.loadInt softirqPendingAddress 2 = some 0)
    (preemptApart : ∀ a, InRange preemptCountAddress 4 a → ¬InRange (s.regs.rsp.toBitVec-8) 8 a)
    (pendingApart : (count+1-512) &&& 0x00ffff00 = 0 →
      ∀ a, InRange softirqPendingAddress 2 a → ¬InRange (s.regs.rsp.toBitVec-8) 8 a)
    (history : List MachineState) (events seen : List Point) (source : List MirrorHistory.Point)
    (observed : observeHistory (LookupObservation.edge c.rxSection) history = .ok events)
    (related : R c history seen ⟨s, Image.Lookup.entry+0x78⟩ world)
    (fullObserved : observe c.rxSection history = .ok seen)
    (matched : MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection history) seen source)
    (cutsAligned : ExecutedCorrespondence.CutsAligned (R c) c.rxSection history source)
    (latest : source.getLast?.map (·.world) = some world)
    (inactive : helperActive seen = false) (noReturn : lastHelperReturn seen = none)
    (apart : ∀ v, project c world = some v → ∀ a, Reads c v a →
      ¬(InRange (s.regs.rsp.toBitVec-8) 8 a ∨ InRange preemptCountAddress 4 a)) :
    Eventually (historyStep fetch) (fun final =>
      Returned (LookupBh.called s) final.machine (Image.Lookup.entry+0x89).toUInt64 ∧
      final.machine.data.dmem.loadInt preemptCountAddress 4 = some ((count-512).toNat : Int) ∧
      EqualOutside (fun a => InRange (s.regs.rsp.toBitVec-8) 8 a ∨ InRange preemptCountAddress 4 a)
        s.dmem final.machine.data.dmem ∧
      observe c.rxSection final.history = .ok seen ∧
      MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection final.history) seen source ∧
      ExecutedCorrespondence.CutsAligned (R c) c.rxSection final.history source ∧
      R c final.history seen final.machine world ∧
      ∃ suffix, final.history = history ++ suffix ∧
        ∀ q ∈ suffix, q.pc ∈ Image.cutPoints →
          EqualOutside (fun a => InRange (s.regs.rsp.toBitVec-8) 8 a ∨ InRange preemptCountAddress 4 a)
            s.dmem q.data.dmem)
      ⟨⟨s, Image.Lookup.entry+0x78⟩, history⟩ := by
  have run := LookupBh.enable_history fetch agree contract s count aligned mapped preempt hardirq pending
    preemptApart pendingApart c.rxSection history events observed related.1
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
  rintro final ⟨ret, balanced, frame, raw, last, tail, recorded, localLast, noReentry⟩
  let suffix := LookupBh.argumentStates s ++ tail
  have full : observe c.rxSection (history ++ suffix) = .ok seen := by
    have h := observe_extend_raw c.rxSection history suffix seen events [] fullObserved observed (by
      simpa only [suffix, List.append_nil, List.append_assoc, recorded] using raw)
    simpa only [List.append_nil] using h
  have frames : ∀ q ∈ suffix, q.pc ∈ Image.cutPoints →
      EqualOutside (fun a => InRange (s.regs.rsp.toBitVec-8) 8 a ∨ InRange preemptCountAddress 4 a)
        s.dmem q.data.dmem := by
    intro q member cut
    rcases List.mem_append.mp member with args | service
    · simp only [LookupBh.argumentStates, List.mem_cons, List.not_mem_nil, or_false] at args
      rcases args with rfl | rfl | rfl
      · intro a _; rfl
      · intro a _; rfl
      · exact False.elim (by simpa [LookupBh.called, Instrumentation.calledState, Image.cutPoints] using cut)
    · have member : q ∈ LookupBh.called s :: tail := List.mem_cons_of_mem _ service
      rw [← history_restore localLast] at member
      rcases List.mem_append.mp member with interior | lastState
      · exact False.elim (no_reentry_cuts _ noReentry q interior cut)
      · have eq : q = final.machine := List.mem_singleton.mp lastState
        simpa only [eq] using frame
  have composed := silent_suffix c world _ final.machine history suffix seen source related fullObserved full
    matched cutsAligned latest inactive noReturn (by simpa only [suffix, recorded, List.append_assoc] using last)
    _ frames frame apart
  refine ⟨ret, balanced, frame, ?_, ?_, ?_, ?_, suffix, ?_, frames⟩
  · simpa only [suffix, recorded, List.append_assoc] using full
  · simpa only [suffix, recorded, List.append_assoc] using composed.1
  · simpa only [suffix, recorded, List.append_assoc] using composed.2.1
  · simpa only [suffix, recorded, List.append_assoc] using composed.2.2
  · simpa only [suffix, List.append_assoc] using recorded

#print axioms bh_simulation
end Binary.LookupRelation
