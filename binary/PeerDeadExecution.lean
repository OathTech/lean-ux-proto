import PeerReturningSimulation
import PeerDeadEntryHistory

namespace Binary.LookupRelation
open Leanux Leanux.WG TrustBase LookupHistory LookupObservation PeerCountPhase
local instance : Labels := Image.linkedLabels

/-- The dead-peer branch includes every helper decision/cut and commits
    its actual zero result. The caller still owes NULL store-back. -/
theorem dead_helper_execution (c : Config) (world : World) (device : Device)
    (pid : PeerId) (peer : Peer)
 (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (contract : TracePcContract fetch)
    (traceCmp : TraceConstCmp4Contract fetch)
    (s : MachineData) (returnAddress : UInt64)
    (entry : EntryFrame ⟨s, Image.PeerGet.entry⟩ returnAddress) (nonnull : s.regs.rdi ≠ 0)
    (field : s.dmem.loadInt (s.regs.rdi.toBitVec+0x420) 4 = some 0)
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
    (fieldSeparate : ∀ a, InRange (s.regs.rdi.toBitVec+0x420) 4 a → ¬PeerGet.entryWrites s coverage a)
    (comparison : coverage.CompareAllowed preempt)
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
    (focused : c.focus.peer = some pid) (pointer : s.regs.rdi.toBitVec = c.peers pid)
    (hasDevice : world.k.wg = some device) (hasPeer : device.peers.get? pid = some peer)
    (sourceZero : peer.refcount = 0)
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
          (sourceHistory ++ MirrorHistory.peerPoints world peer ++
            [⟨.returned "wg_peer_get_maybe_zero", PeerMirror.peerFinal pid world peer⟩]) ∧
        ExecutedCorrespondence.CutsAligned (R c) c.rxSection final.history
          (sourceHistory ++ MirrorHistory.peerPoints world peer ++
            [⟨.returned "wg_peer_get_maybe_zero", PeerMirror.peerFinal pid world peer⟩]) ∧
        R c final.history points final.machine (PeerMirror.peerFinal pid world peer) ∧
        ∃ tail, final.history = history ++ tail ∧
          ∀ q ∈ tail, q.pc ∈ Image.cutPoints →
            EqualOutside (PeerGet.entryWrites s coverage) s.dmem q.data.dmem)
      ⟨⟨s, Image.PeerGet.entry⟩, history⟩ := by
  have run := PeerGet.dead_entry_history fetch agree contract traceCmp s returnAddress entry nonnull
    field coverage preempt state phase mapped pushSeparate coverageSeparate metadataSeparate
    preemptSeparate fieldSeparate comparison c.rxSection history events observed last
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
  rintro final ⟨returned, result, ready, frame, lastFinal, phaseAt,
    nullPoint, zeroPoint, negative, wrap, dead, _, _, _, _, _, rawFull, tail, recorded, frames⟩
  let delta := peerDecisions c.rxSection peer.refcount nullPoint zeroPoint zeroPoint negative wrap dead
  have rawSeen : observeHistory (edge c.rxSection) final.history =
      .ok (events ++ delta ++ [LookupObservation.returned "wg_peer_get_maybe_zero" final.machine]) := by
    simpa [delta, peerDecisions, sourceZero, List.append_assoc] using rawFull
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
    matched aligned latest (peerDecisions_tags _ _ _ _ _ _ _ _) (peerDecisions_helper_tags _ _ _ _ _ _ _ _)
    active noReturn (by simpa only [recorded] using phaseAt) splitHistory initial (PeerGet.entryWrites s coverage) frames apart
  have finalProjection : project c (PeerMirror.peerFinal pid world peer) = project c world := by
    obtain ⟨v, projected, _⟩ := related.2.1
    have h := project_peerFinal c world device pid peer v hasDevice hasPeer focused projected
    simpa only [sourceZero, ite_true, ← projected] using h
  have finalLog := peer_final_log world peer pid nullPoint zeroPoint zeroPoint negative wrap dead
  have sameRx := finalLog.2
  rw [related.2.2.2] at finalLog
  have endpoint := unchanged_return_related c world (PeerMirror.peerFinal pid world peer)
    ⟨s, Image.PeerGet.entry⟩ final.machine history final.history seen delta related finalProjection finalLog.1 sameRx
    initial noReturn lastFinal (returned.1.trans returnPC) _ frame apart
  have all := helper_return_compose c (history ++ interior) (seen ++ delta)
    (sourceHistory ++ LookupSearch.decisionWorlds world (delta.filterMap (·.step))) final.machine
    (PeerMirror.peerFinal pid world peer) interiorProof.1 interiorProof.2
    (by simpa only [splitHistory, ← recorded] using full)
    (by simpa only [splitHistory, ← recorded] using endpoint)
  have worlds : LookupSearch.decisionWorlds world (delta.filterMap (·.step)) = MirrorHistory.peerPoints world peer := by
    dsimp only [delta]
    rw [← related.2.2.2]
    exact peer_decision_worlds _ _ _ _ _ _ _ _
  refine ⟨returned, result, ready, frame, _, full, ?_, ?_, ?_, endpoint, tail, recorded, frames⟩
  · simp [lastHelperReturn, LookupObservation.returned]
  · simpa only [splitHistory, ← recorded, worlds] using all.1
  · simpa only [splitHistory, ← recorded, worlds] using all.2

#print axioms dead_helper_execution
end Binary.LookupRelation
