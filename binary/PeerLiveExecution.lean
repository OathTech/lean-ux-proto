import SourceAdapter
import PeerLiveSimulation
import PeerLiveEntryHistory

namespace Binary.LookupRelation
open Leanux Leanux.WG TrustBase LookupHistory LookupObservation PeerCountPhase
local instance : Labels := Image.linkedLabels

/-- Live peer-get, from its actual CALL entry to RET into lookup, including
    every semantic point and stuttering cut. This is an internal composition
    theorem: lookup must discharge its ABI, callback and separation premises
    from Pre_lookup. The dead and NULL branches are separate obligations. -/
theorem live_helper_execution (c : Config) (world : World) (device : Device)
    (pid : PeerId) (peer : Peer)
 (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (contract : TracePcContract fetch)
    (traceCmp : TraceConstCmp4Contract fetch) (traceByte : TraceConstCmp1Contract fetch)
    (s : MachineData) (returnAddress : UInt64)
    (entry : EntryFrame ⟨s, Image.PeerGet.entry⟩ returnAddress) (nonnull : s.regs.rdi ≠ 0)
    (count : UInt32) (nonzero : count ≠ 0) (bound : count.toNat+1 < 2^31)
    (field : s.dmem.loadInt (s.regs.rdi.toBitVec+0x420) 4 = some count.toNat)
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
    (countSeparate : ∀ a, LookupCoverage.Context.bytes coverage a → ¬InRange (s.regs.rdi.toBitVec+0x420) 4 a)
    (fieldSeparate : ∀ a, InRange (s.regs.rdi.toBitVec+0x420) 4 a →
      ¬(InRange (s.regs.rsp.toBitVec-56) 64 a ∨ LookupCoverage.Context.writes coverage a))
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
    (hasDevice : world.wg.dev = some device) (hasPeer : device.peers.get? pid = some peer)
    (sourceCount : peer.refcount = count.toNat)
    (returnPC : Int64.ofBitVec returnAddress.toBitVec = Image.Lookup.entry+0xba)
    (initial : scan none history = none)
    (seed : Pending) (incoming : ∀ n, scan (some seed) (history.take n) ≠ none)
    (bucketApart : ∀ v, project c world = some v → ∀ a, LookupBucketBytes c v a →
      ¬(InRange (s.regs.rdi.toBitVec+0x420) 4 a ∨ PeerGet.entryWrites s coverage a))
    (ownerApart : ∀ a, LookupOwnerBytes c a →
      ¬(InRange (s.regs.rdi.toBitVec+0x420) 4 a ∨ PeerGet.entryWrites s coverage a)) :
    Eventually (historyStep fetch) (fun final =>
      Returned ⟨s, Image.PeerGet.entry⟩ final.machine returnAddress ∧
      PeerGet.ScratchMapped s final.machine.data.dmem ∧
      final.machine.data.regs.rax = s.regs.rdi ∧
      LookupCoverage.Context.At coverage preempt final.machine.data.dmem ∧
      EqualOutside (fun a => InRange (s.regs.rdi.toBitVec+0x420) 4 a ∨ PeerGet.entryWrites s coverage a)
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
            EqualOutside (fun a => InRange (s.regs.rdi.toBitVec+0x420) 4 a ∨ PeerGet.entryWrites s coverage a)
              s.dmem q.data.dmem)
      ⟨⟨s, Image.PeerGet.entry⟩, history⟩ := by
  have run := PeerGet.live_entry_history fetch agree contract traceCmp traceByte s returnAddress entry nonnull
    count nonzero bound field coverage preempt state phase mapped pushSeparate coverageSeparate metadataSeparate
    preemptSeparate countSeparate fieldSeparate comparison c.rxSection history events observed last
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
  rintro final ⟨returned, scratch, result, ready, finalCount, frame, lastFinal, phaseAny,
    nullPoint, zeroPoint, retry, negative, wrap, dead, _, _, _, _, _, _, rawFull,
    before, after, recorded, oldFrames, newFrames, phaseAt⟩
  have countNonzero : count.toNat ≠ 0 := by
    intro zero
    apply nonzero
    exact UInt32.toNat_inj.mp zero
  have boolNonzero : (count.toNat == 0) = false := by
    change decide (count.toNat = 0) = false
    simp only [countNonzero, decide_false]
  have sourceNonzero : peer.refcount ≠ 0 := by simpa only [sourceCount] using countNonzero
  let delta := peerDecisions c.rxSection peer.refcount nullPoint zeroPoint retry negative wrap dead
  have rawSeen : observeHistory (edge c.rxSection) final.history =
      .ok (events ++ delta ++ [LookupObservation.returned "wg_peer_get_maybe_zero" final.machine]) := by
    simpa [delta, peerDecisions, sourceCount, countNonzero, boolNonzero, List.append_assoc] using rawFull
  have full : observe c.rxSection final.history =
      .ok ((seen ++ delta) ++ [LookupObservation.returned "wg_peer_get_maybe_zero" final.machine]) := by
    rw [recorded] at rawSeen ⊢
    simpa only [List.append_assoc] using observe_extend_raw c.rxSection history (before ++ after)
      seen events (delta ++ [LookupObservation.returned "wg_peer_get_maybe_zero" final.machine])
      fullObserved observed (by simpa only [List.append_assoc] using rawSeen)
  have frontObs := helper_return_prefix c.rxSection final.history final.machine (seen ++ delta) seed lastFinal
    (phaseAt.nonempty_before_return seed incoming) (phaseAt.final (some seed)) full
  have prefixed : history.IsPrefix final.history.dropLast := by
    obtain ⟨body, af, stable, _, _, _, tail, tailNonempty, finalEq, _⟩ := phaseAt
    obtain ⟨initialTail, boundaryEq, _⟩ := stable
    rw [finalEq, List.dropLast_append_of_ne_nil tailNonempty, boundaryEq, List.append_assoc, List.append_assoc]
    exact List.prefix_append _ _
  obtain ⟨interior, interiorEq⟩ := prefixed
  have splitHistory : (history ++ interior) ++ [final.machine] = history ++ before ++ after := by
    rw [interiorEq, history_restore lastFinal, ← recorded]
  have fieldAddr : s.regs.rdi.toBitVec+0x420 = c.peers pid + .ofNat 64 Layouts.peer_refcount := by rw [pointer]; rfl
  have scratchApart : ∀ j < 4, ¬PeerGet.entryWrites s coverage
      (c.peers pid + .ofNat 64 Layouts.peer_refcount + .ofNat 64 j) := by
    intro j hj written
    apply fieldSeparate _ (by rw [fieldAddr]; exact ⟨j, hj, rfl⟩)
    rcases written with stack | buffer
    · obtain ⟨i, hi, eq⟩ := stack
      exact .inl ⟨i, by omega, eq⟩
    · exact .inr buffer
  change s.dmem.loadInt (s.regs.rdi.toBitVec+0x420) 4 = some (count.toNat : Int) at field
  have interiorProof := live_interior c world ⟨s, Image.PeerGet.entry⟩ history before after interior final.machine
    seen delta sourceHistory related fullObserved (by simpa only [interiorEq] using frontObs)
    matched aligned latest (peerDecisions_tags _ _ _ _ _ _ _ _) (peerDecisions_helper_tags _ _ _ _ _ _ _ _)
    active noReturn pid focused count.toBitVec
    (by simpa only [recorded, fieldAddr] using phaseAt) splitHistory initial
    (by simpa only [fieldAddr, UInt32.toNat_toBitVec] using field)
    (PeerGet.entryWrites s coverage) scratchApart (by simp only [UInt32.toNat_toBitVec]; omega)
    oldFrames (by simpa only [PeerGet.incrementEntryMemory, fieldAddr] using newFrames)
    (by simpa only [fieldAddr] using bucketApart) (by simpa only [fieldAddr] using ownerApart)
  have increment : (count.toBitVec+1).toNat = peer.refcount+1 := by
    simp only [BitVec.toNat_add, UInt32.toNat_toBitVec, show (1 : BitVec 32).toNat = 1 from rfl, sourceCount]
    exact Nat.mod_eq_of_lt (by omega)
  have endpoint := live_return_related c world device pid peer ⟨s, Image.PeerGet.entry⟩ final.machine
    history final.history seen nullPoint zeroPoint retry negative wrap dead related hasDevice hasPeer focused
    sourceNonzero noReturn lastFinal (returned.1.trans returnPC) _ frame bucketApart ownerApart
    (by simpa only [fieldAddr, increment, Int.natCast_add_one] using finalCount)
  have all := helper_return_compose c (history ++ interior) (seen ++ delta)
    (sourceHistory ++ LookupSearch.decisionWorlds world (delta.filterMap (·.step))) final.machine
    (PeerMirror.peerFinal pid world peer) interiorProof.1 interiorProof.2
    (by simpa only [splitHistory, ← recorded] using full)
    (by simpa only [splitHistory, ← recorded] using endpoint)
  have worlds : LookupSearch.decisionWorlds world (delta.filterMap (·.step)) = MirrorHistory.peerPoints world peer := by
    dsimp only [delta]
    rw [← related.2.2.2]
    exact peer_decision_worlds _ _ _ _ _ _ _ _
  refine ⟨returned, scratch, result, ready, frame, _, full, ?_, ?_, ?_, endpoint,
    before ++ after, by simpa only [List.append_assoc] using recorded, ?_⟩
  · simp [lastHelperReturn, LookupObservation.returned]
  · simpa only [splitHistory, ← recorded, worlds] using all.1
  · simpa only [splitHistory, ← recorded, worlds] using all.2
  · intro q member cut
    rcases List.mem_append.mp member with old | incremented
    · intro a outside
      exact oldFrames q old cut a (fun written => outside (.inr written))
    · exact (storeInt_frame s.dmem _ 4 _).trans
        (by simpa only [PeerGet.incrementEntryMemory] using newFrames q incremented cut)

#print axioms live_helper_execution
end Binary.LookupRelation
