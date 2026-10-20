import SourceAdapter
import PeerLiveExecution
import PeerDeadExecution
import PeerNullExecution

namespace Binary.LookupRelation
open Leanux Leanux.WG TrustBase LookupHistory LookupObservation PeerCountPhase
local instance : Labels := Image.linkedLabels

/-- Both present-peer paths, with the arithmetic bound derived from the
    actual mirror's acceptance. Dead-peer entries remain in the domain. -/
theorem accepted_nonnull_helper_execution (c : Config) (world : World) (device : Device)
    (pid : PeerId) (peer : Peer)
 (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (contract : TracePcContract fetch)
    (traceCmp : TraceConstCmp4Contract fetch) (traceByte : TraceConstCmp1Contract fetch)
    (s : MachineData) (returnAddress : UInt64)
    (entry : EntryFrame ⟨s, Image.PeerGet.entry⟩ returnAddress) (nonnull : s.regs.rdi ≠ 0)
    (answer : Option PeerId) (worldFinal : World)
    (accepted : (Source.peerGetMaybeZero (some pid)).run world = .ok (answer, worldFinal))
    (field : s.dmem.loadInt (s.regs.rdi.toBitVec+0x420) 4 = some (peer.refcount : Int))
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
    (countSeparate : peer.refcount ≠ 0 → ∀ a, LookupCoverage.Context.bytes coverage a → ¬InRange (s.regs.rdi.toBitVec+0x420) 4 a)
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
    (returnPC : Int64.ofBitVec returnAddress.toBitVec = Image.Lookup.entry+0xba)
    (initial : scan none history = none)
    (seed : Pending) (incoming : ∀ n, scan (some seed) (history.take n) ≠ none)
    (bucketApart : ∀ v, project c world = some v → ∀ a, LookupBucketBytes c v a →
      ¬((peer.refcount ≠ 0 ∧ InRange (s.regs.rdi.toBitVec+0x420) 4 a) ∨ PeerGet.entryWrites s coverage a))
    (ownerApart : ∀ a, LookupOwnerBytes c a →
      ¬(InRange (s.regs.rdi.toBitVec+0x420) 4 a ∨ PeerGet.entryWrites s coverage a)) :
    Eventually (historyStep fetch) (fun final =>
      Returned ⟨s, Image.PeerGet.entry⟩ final.machine returnAddress ∧
      (answer.isSome = true → PeerGet.ScratchMapped s final.machine.data.dmem) ∧
      final.machine.data.regs.rax = (if answer.isSome then s.regs.rdi else 0) ∧
      LookupCoverage.Context.At coverage preempt final.machine.data.dmem ∧
      EqualOutside (fun a => (peer.refcount ≠ 0 ∧ InRange (s.regs.rdi.toBitVec+0x420) 4 a) ∨ PeerGet.entryWrites s coverage a)
        s.dmem final.machine.data.dmem ∧
      ∃ points, observe c.rxSection final.history = .ok points ∧
        lastHelperReturn points = some final.machine ∧
        MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection final.history) points
          (sourceHistory ++ MirrorHistory.peerPoints world peer ++
            [⟨.returned "wg_peer_get_maybe_zero", worldFinal⟩]) ∧
        ExecutedCorrespondence.CutsAligned (R c) c.rxSection final.history
          (sourceHistory ++ MirrorHistory.peerPoints world peer ++
            [⟨.returned "wg_peer_get_maybe_zero", worldFinal⟩]) ∧
        R c final.history points final.machine worldFinal ∧
        ∃ tail, final.history = history ++ tail ∧
          ∀ q ∈ tail, q.pc ∈ Image.cutPoints →
            EqualOutside (fun a => (peer.refcount ≠ 0 ∧ InRange (s.regs.rdi.toBitVec+0x420) 4 a) ∨
              PeerGet.entryWrites s coverage a) s.dmem q.data.dmem)
      ⟨⟨s, Image.PeerGet.entry⟩, history⟩ := by
  have bound := PeerMirror.accepted_peer_bound pid world worldFinal answer device peer hasDevice hasPeer accepted
  obtain ⟨answerEq, finalEq⟩ := PeerMirror.accepted_peer_result pid world worldFinal answer device peer hasDevice hasPeer accepted
  subst worldFinal
  by_cases zero : peer.refcount = 0
  · have run := dead_helper_execution c world device pid peer fetch agree contract traceCmp s returnAddress entry nonnull
      (by simpa only [zero, Int.natCast_zero] using field) coverage preempt state phase mapped pushSeparate
      coverageSeparate metadataSeparate preemptSeparate (by
        intro a inside written
        apply fieldSeparate a inside
        rcases written with stack | buffer
        · obtain ⟨i, hi, eq⟩ := stack
          exact .inl ⟨i, by omega, eq⟩
        · exact .inr buffer)
      comparison history events observed last seen sourceHistory related fullObserved matched aligned latest
      active noReturn focused pointer hasDevice hasPeer zero returnPC initial seed incoming (by
        intro v projected a read written
        rcases read with head | node | owner | count
        · exact bucketApart v projected a (.inl head) (.inr written)
        · exact bucketApart v projected a (.inr node) (.inr written)
        · exact ownerApart a owner (.inr written)
        · obtain ⟨other, focusOther, j, hj, eq⟩ := count
          have same : other = pid := Option.some.inj (focusOther.symm.trans focused)
          subst other
          apply fieldSeparate a (by rw [pointer]; exact ⟨j, hj, eq⟩)
          rcases written with stack | buffer
          · obtain ⟨i, hi, eq⟩ := stack
            exact .inl ⟨i, by omega, eq⟩
          · exact .inr buffer)
    apply eventually_weaken (historyStep fetch) _ _ _ _ run
    rintro final ⟨ret, result, ready, frame, points, full, returned, matched, cuts, related,
      tail, recorded, frames⟩
    refine ⟨ret, ?_, ?_, ready, ?_, points, full, returned, matched, cuts, related,
      tail, recorded, ?_⟩
    · simp [answerEq, zero]
    · simpa only [answerEq, zero, ite_true, Option.isSome_none, Bool.false_eq_true, ite_false] using result
    · intro a outside
      exact frame a (fun written => outside (.inr written))
    · intro q member cut a outside
      exact frames q member cut a (fun written => outside (.inr written))
  · let count := UInt32.ofNat peer.refcount
    have countNat : count.toNat = peer.refcount := by
      simp only [count]
      exact Nat.mod_eq_of_lt (by omega)
    have countNonzero : count ≠ 0 := by
      intro equal
      have h := congrArg UInt32.toNat equal
      rw [countNat] at h
      exact zero h
    have run := live_helper_execution c world device pid peer fetch agree contract traceCmp traceByte s returnAddress entry
      nonnull count countNonzero (by simpa only [countNat] using bound) (by
        change s.dmem.loadInt (s.regs.rdi.toBitVec+0x420) 4 = some (count.toNat : Int)
        simpa only [countNat] using field)
      coverage preempt state phase mapped pushSeparate coverageSeparate metadataSeparate preemptSeparate (countSeparate zero)
      fieldSeparate comparison history events observed last seen sourceHistory related fullObserved matched aligned latest
      active noReturn focused pointer hasDevice hasPeer countNat.symm returnPC initial seed incoming (by
        intro v projected a read written
        apply bucketApart v projected a read
        rcases written with count | scratch
        · exact .inl ⟨zero, count⟩
        · exact .inr scratch) ownerApart
    apply eventually_weaken (historyStep fetch) _ _ _ _ run
    rintro final ⟨ret, scratch, result, ready, frame, points, full, returned, matched, cuts, related,
      tail, recorded, frames⟩
    refine ⟨ret, fun _ => scratch, ?_, ready, ?_, points, full, returned, matched, cuts, related,
      tail, recorded, ?_⟩
    · simpa only [answerEq, ite_eq_right zero, Option.isSome_some, ite_true] using result
    · intro a outside
      apply frame a
      rintro (count | scratch)
      · exact outside (.inl ⟨zero, count⟩)
      · exact outside (.inr scratch)
    · intro q member cut a outside
      apply frames q member cut a
      rintro (count | scratch)
      · exact outside (.inl ⟨zero, count⟩)
      · exact outside (.inr scratch)

#print axioms accepted_nonnull_helper_execution
end Binary.LookupRelation
