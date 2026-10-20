import PeerReturningSimulation
import PeerNullEntryHistory

namespace Binary.LookupRelation
open Leanux Leanux.WG TrustBase LookupHistory LookupObservation PeerCountPhase
local instance : Labels := Image.linkedLabels

/-- The NULL helper branch, including every actual cut and its single
    source decision; no peer count is loaded or constrained by this branch. -/
theorem null_helper_execution (c : Config) (world : World)
 (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (contract : TracePcContract fetch)
    (s : MachineData) (returnAddress : UInt64)
    (entry : EntryFrame ⟨s, Image.PeerGet.entry⟩ returnAddress) (null : s.regs.rdi = 0)
    (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (state : LookupCoverage.Context.At coverage preempt s.dmem)
    (phase : preempt = coverage.entryPreempt ∨ preempt = 512+coverage.entryPreempt)
    (mapped : ∀ n < 7,
      (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true)
    (pushSeparate : ∀ address, LookupCoverage.Context.bytes coverage address →
      ¬InRange (s.regs.rsp.toBitVec-56) 56 address)
    (coverageSeparate : LookupCoverage.Context.Separated coverage (InRange (s.regs.rsp.toBitVec-56) 64))
    (metadataSeparate : LookupCoverage.Context.Separated coverage (LookupCoverage.Context.metadataBytes coverage))
    (preemptSeparate : LookupCoverage.Context.Separated coverage (InRange preemptCountAddress 4))
    (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge c.rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s, Image.PeerGet.entry⟩)
    (seen : List Point) (sourceHistory : List MirrorHistory.Point)
    (related : R c history seen ⟨s, Image.PeerGet.entry⟩ world)
    (fullObserved : observe c.rxSection history = .ok seen)
    (matched : MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection history) seen sourceHistory)
    (aligned : ExecutedCorrespondence.CutsAligned (R c) c.rxSection history sourceHistory)
    (latest : sourceHistory.getLast?.map (·.world) = some world)
    (active : helperActive seen = true) (noReturn : lastHelperReturn seen = none)
    (returnPC : Int64.ofBitVec returnAddress.toBitVec = Image.Lookup.entry+0xba)
    (initial : scan none history = none)
    (seed : Pending) (incoming : ∀ n, scan (some seed) (history.take n) ≠ none)
    (apart : ∀ v, project c world = some v → ∀ a, Reads c v a → ¬PeerGet.entryWrites s coverage a) :
    Eventually (historyStep fetch) (fun final =>
      Returned ⟨s, Image.PeerGet.entry⟩ final.machine returnAddress ∧
      final.machine.data.regs.rax = 0 ∧
      LookupCoverage.Context.At coverage preempt final.machine.data.dmem ∧
      EqualOutside (PeerGet.entryWrites s coverage)
        s.dmem final.machine.data.dmem ∧
      ∃ points, observe c.rxSection final.history = .ok points ∧
        lastHelperReturn points = some final.machine ∧
        MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection final.history) points
          (sourceHistory ++ [⟨.decision .peerGetMaybeZeroNull, LookupMirror.record world .peerGetMaybeZeroNull true⟩] ++
            [⟨.returned "wg_peer_get_maybe_zero", LookupMirror.record world .peerGetMaybeZeroNull true⟩]) ∧
        ExecutedCorrespondence.CutsAligned (R c) c.rxSection final.history
          (sourceHistory ++ [⟨.decision .peerGetMaybeZeroNull, LookupMirror.record world .peerGetMaybeZeroNull true⟩] ++
            [⟨.returned "wg_peer_get_maybe_zero", LookupMirror.record world .peerGetMaybeZeroNull true⟩]) ∧
        R c final.history points final.machine (LookupMirror.record world .peerGetMaybeZeroNull true) ∧
        ∃ tail, final.history = history ++ tail ∧
          ∀ q ∈ tail, q.pc ∈ Image.cutPoints →
            EqualOutside (PeerGet.entryWrites s coverage) s.dmem q.data.dmem)
      ⟨⟨s, Image.PeerGet.entry⟩, history⟩ := by
  have run := PeerGet.null_entry_history fetch agree contract s returnAddress entry null
    coverage preempt state phase mapped pushSeparate coverageSeparate metadataSeparate
    preemptSeparate c.rxSection history events observed last
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
  rintro final ⟨returned, result, ready, frame, lastFinal, phaseAt,
    guard, _, _, rawFull, tail, recorded, frames⟩
  let delta := [decision c.rxSection .peerGetMaybeZeroNull true guard]
  have tags : LookupHistory.DecisionPoints delta := by
    intro p member
    have eq := List.mem_singleton.mp member
    subst p
    exact ⟨_, rfl, rfl⟩
  have helperTags : ∀ p ∈ delta, HelperTag p.tag := by
    intro p member
    have eq := List.mem_singleton.mp member
    subst p
    simp [decision, HelperTag]
  have rawSeen : observeHistory (edge c.rxSection) final.history =
      .ok (events ++ delta ++ [LookupObservation.returned "wg_peer_get_maybe_zero" final.machine]) := by
    simpa only [delta, List.append_assoc, List.singleton_append] using rawFull
  have full : observe c.rxSection final.history =
      .ok ((seen ++ delta) ++ [LookupObservation.returned "wg_peer_get_maybe_zero" final.machine]) := by
    rw [recorded] at rawSeen ⊢
    simpa only [List.append_assoc] using observe_extend_raw c.rxSection history tail
      seen events (delta ++ [LookupObservation.returned "wg_peer_get_maybe_zero" final.machine])
      fullObserved observed (by simpa only [List.append_assoc] using rawSeen)
  have frontObs := helper_return_prefix c.rxSection final.history final.machine (seen ++ delta) seed lastFinal
    (phaseAt.nonempty_before_return seed incoming) (phaseAt.final (some seed)) full
  have prefixed : history.IsPrefix final.history.dropLast := by
    obtain ⟨rest, nonempty, finalEq, _⟩ := phaseAt
    rw [finalEq, List.dropLast_append_of_ne_nil nonempty]
    exact List.prefix_append _ _
  obtain ⟨interior, interiorEq⟩ := prefixed
  have splitHistory : (history ++ interior) ++ [final.machine] = history ++ tail := by
    rw [interiorEq, history_restore lastFinal, ← recorded]
  have interiorProof := returning_interior c world ⟨s, Image.PeerGet.entry⟩ history tail interior final.machine
    seen delta sourceHistory related fullObserved (by simpa only [interiorEq] using frontObs)
    matched aligned latest tags helperTags
    active noReturn (by simpa only [recorded] using phaseAt) splitHistory initial (PeerGet.entryWrites s coverage) frames apart
  have finalProjection : project c (LookupMirror.record world .peerGetMaybeZeroNull true) = project c world := rfl
  have finalSteps : (LookupMirror.record world .peerGetMaybeZeroNull true).steps =
      (LookupSearch.advance world (delta.filterMap (·.step))).steps := by
    dsimp only [delta]
    rw [← related.2.2.2]
    rfl
  have endpoint := unchanged_return_related c world (LookupMirror.record world .peerGetMaybeZeroNull true)
    ⟨s, Image.PeerGet.entry⟩ final.machine history final.history seen delta related finalProjection finalSteps rfl
    initial noReturn lastFinal (returned.1.trans returnPC) _ frame apart
  have all := helper_return_compose c (history ++ interior) (seen ++ delta)
    (sourceHistory ++ LookupSearch.decisionWorlds world (delta.filterMap (·.step))) final.machine
    (LookupMirror.record world .peerGetMaybeZeroNull true) interiorProof.1 interiorProof.2
    (by simpa only [splitHistory, ← recorded] using full)
    (by simpa only [splitHistory, ← recorded] using endpoint)
  have worlds : LookupSearch.decisionWorlds world (delta.filterMap (·.step)) =
      [⟨.decision .peerGetMaybeZeroNull, LookupMirror.record world .peerGetMaybeZeroNull true⟩] := by
    dsimp only [delta]
    rw [← related.2.2.2]
    rfl
  refine ⟨returned, result, ready, frame, _, full, ?_, ?_, ?_, endpoint, tail, recorded, frames⟩
  · simp [lastHelperReturn, LookupObservation.returned]
  · simpa only [splitHistory, ← recorded, worlds] using all.1
  · simpa only [splitHistory, ← recorded, worlds] using all.2

#print axioms null_helper_execution
end Binary.LookupRelation
