import LookupHelperSeparation
import LookupHelperSource
import PeerAcceptedExecution
import LookupOutputMapping

namespace Binary.LookupRelation
open Leanux Leanux.WG TrustBase LookupHistory LookupObservation PeerCountPhase
local instance : Labels := Image.linkedLabels

abbrev helperWorld (c : Config) (world : World) (v : View) : World :=
  (LookupSearch.result c.kinds c.query v.bucket [sourceEntry world] world).2

abbrev helperSource (c : Config) (world : World) (v : View) : List MirrorHistory.Point :=
  (LookupSearch.result c.kinds c.query v.bucket [sourceEntry world] world).1.2 ++
    [⟨.call "wg_peer_get_maybe_zero", helperWorld c world v⟩]

private theorem initial_raw (c : Config) (s : MachineData) (history : List MachineState)
    (events : List Point) (stable : StableExtension [⟨s, Image.Lookup.entry⟩] history)
    (observed : observe c.rxSection history = .ok (entryPoint s :: events)) :
    observeHistory (LookupObservation.edge c.rxSection) history = .ok events := by
  obtain ⟨tail, recorded, _⟩ := stable
  rw [recorded] at observed ⊢
  cases raw : observeHistory (LookupObservation.edge c.rxSection) ([⟨s, Image.Lookup.entry⟩] ++ tail) with
  | error error =>
    simp only [List.singleton_append] at raw
    simp [observe, raw] at observed
    cases observed
  | ok points =>
    simp only [List.singleton_append] at raw
    simp [observe, raw] at observed
    have same : points = events := by
      have h := Except.ok.inj observed
      exact List.cons.inj h |>.2
    exact congrArg Except.ok same

/-- Actual helper-return postcondition, retaining source and physical frames
    needed by the owner/output/outer-return continuation. -/
def AfterHelper (c : Config) (coverage : KcovLayout) (preempt : BitVec 32)
    (s : MachineData) (world : World) (v : View) (current : Executed)
    (answer : Option PeerId) (worldFinal : World) (final : Executed) : Prop :=
      Returned current.machine final.machine (Image.Lookup.entry+0xba).toUInt64 ∧
      (answer.isSome = true → PeerGet.ScratchMapped current.machine.data final.machine.data.dmem) ∧
      (answer.isSome = true → (final.machine.data.dmem.loadInt s.regs.rcx.toBitVec 8).isSome = true) ∧
      (answer.isSome = true → LookupOutputNeeded v) ∧
      (∃ afterView, project c worldFinal = some afterView ∧ afterView.bucket = v.bucket ∧ afterView.ownerWord = v.ownerWord) ∧
      final.machine.data.regs.rax.toBitVec = OwnerWord.pointer c.peers answer ∧
      decide (final.machine.data.regs.rax ≠ 0) = answer.isSome ∧
      LookupCoverage.Context.At ⟨coverage, preempt, v⟩ (512+preempt) final.machine.data.dmem ∧
      EqualOutside (fun a => LookupDataWrites c v a ∨ PeerGet.entryWrites current.machine.data ⟨coverage, preempt, v⟩ a)
        current.machine.data.dmem final.machine.data.dmem ∧
      ∃ sourcePoints points,
        (∀ prior, ((MirrorHistory.peerGet c.focus.peer).run prior).run (helperWorld c world v) = .ok ((answer, prior ++ sourcePoints), worldFinal)) ∧
        observe c.rxSection final.history = .ok points ∧
        lastHelperReturn points = some final.machine ∧
        MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection final.history) points
          (helperSource c world v ++ sourcePoints ++ [⟨.returned "wg_peer_get_maybe_zero", worldFinal⟩]) ∧
        ExecutedCorrespondence.CutsAligned (R c) c.rxSection final.history
          (helperSource c world v ++ sourcePoints ++ [⟨.returned "wg_peer_get_maybe_zero", worldFinal⟩]) ∧
        R c final.history points final.machine worldFinal ∧
        ∃ tail, final.history = current.history ++ tail ∧
          ∀ q ∈ tail, q.pc ∈ Image.cutPoints →
            EqualOutside (fun a => LookupDataWrites c v a ∨
              PeerGet.entryWrites current.machine.data ⟨coverage, preempt, v⟩ a)
              current.machine.data.dmem q.data.dmem

/-- Every helper ABI, mapping and separation premise is now derived from
    the witnessed lookup entry and its actual executed CALL. -/
theorem helper_from_call (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (tracePc : TracePcContract fetch)
    (traceCmp : TraceConstCmp4Contract fetch) (traceByte : TraceConstCmp1Contract fetch)
    (c : Config) (coverage : KcovLayout) (preempt : BitVec 32) (returnAddress : UInt64)
    (s : MachineData) (world : World) (v : View)
    (entry : LookupEntry c coverage preempt returnAddress ⟨s, Image.Lookup.entry⟩ world v)
    (bucket current : Executed) (afterBucket : AfterBucket c world s coverage preempt v bucket)
    (owner : IndexOwner) (focused : c.focus.owner = some owner)
    (before : BeforeHelper c coverage preempt s world v bucket owner current)
    (answer : Option PeerId) (worldFinal : World)
    (accepted : (peerGetMaybeZero c.focus.peer).run (helperWorld c world v) = .ok (answer, worldFinal)) :
    Eventually (historyStep fetch)
      (AfterHelper c coverage preempt s world v current answer worldFinal) current := by
  have savedBefore := before
  obtain ⟨callback, delta, cbPC, cbStack, cbOwner, traced, machine, recorded, abi, state, comparison,
    stable, observed, matched, aligned, related⟩ := before
  have pc : current.machine.pc = Image.PeerGet.entry := by rw [machine]; rfl
  have helperSP : current.machine.data.regs.rsp = s.regs.rsp-48 := by
    rw [machine]
    simp only [peerCalled, Instrumentation.calledState, peerArgument, MachineData.setReg, Reg64s.set, Reg64s.set64]
    rw [cbStack]
    apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_sub]
    rw [BitVec.sub_sub]
    rfl
  have pointer : current.machine.data.regs.rdi.toBitVec = OwnerWord.pointer c.peers c.focus.peer := by
    rw [machine]
    exact (peer_call_entry callback.machine.data _ traced.frame.ready.aligned).2
  have mapped := helper_stack_mapped c coverage preempt returnAddress s world v entry bucket afterBucket owner focused
    callback delta traced (OwnerWord.pointer c.peers c.focus.peer)
  rw [← machine] at mapped
  have separate := helper_separation_from_entry c coverage preempt returnAddress s world v entry owner focused current.machine.data helperSP
  let seen := ([entryPoint s] ++ delta) ++ [call "wg_peer_get_maybe_zero" current.machine]
  have raw : observeHistory (LookupObservation.edge c.rxSection) current.history =
      .ok (delta ++ [call "wg_peer_get_maybe_zero" current.machine]) :=
    initial_raw c s current.history _ stable (by simpa only [List.singleton_append, List.cons_append, List.nil_append] using observed)
  have initial : scan none current.history = none := by rw [stable.final none]; rfl
  let seed : Pending := ⟨0, 0⟩
  have incoming := stable.nonempty_prefixes seed (by
    intro n
    cases n <;> simp [scan])
  have active : helperActive seen = true := helperActive_call _ _
  have noReturn : lastHelperReturn seen = none := by simp only [seen, lastHelperReturn, List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.bind_some, call]; rfl
  have latest : (helperSource c world v).getLast?.map (·.world) = some (helperWorld c world v) := by
    simp only [helperSource, List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.map_some]
  have projected : project c (helperWorld c world v) = some v := by
    calc
      _ = project c {world with steps := (helperWorld c world v).steps} :=
        congrArg (project c) (LookupSearch.result_world _ _ _ _ _)
      _ = project c world := rfl
      _ = some v := entry.projected
  have scratch : ∀ view, project c (helperWorld c world v) = some view → ∀ a, Reads c view a →
      ¬PeerGet.entryWrites current.machine.data ⟨coverage, preempt, v⟩ a := by
    intro view projection a read
    have same : view = v := Option.some.inj (projection.symm.trans projected)
    subst view
    exact separate.reads a read
  have last : current.history.getLast? = some ⟨current.machine.data, Image.PeerGet.entry⟩ := by
    simpa only [← pc] using related.1
  have cursor : (⟨⟨current.machine.data, Image.PeerGet.entry⟩, current.history⟩ : Executed) = current := by rw [← pc]
  cases focusPeer : c.focus.peer with
  | none =>
    have null : current.machine.data.regs.rdi = 0 := by
      apply UInt64.toBitVec_inj.mp
      simpa [focusPeer, OwnerWord.pointer] using pointer
    rw [focusPeer, PeerMirror.peer_null_run] at accepted
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj accepted.symm)
    have run := null_helper_execution c (helperWorld c world v) fetch agree tracePc current.machine.data _
      (by simpa only [← pc] using abi) null ⟨coverage, preempt, v⟩ (512+preempt) state (.inr rfl) mapped
      separate.push separate.stack separate.metadata separate.preempt current.history _ raw last
      seen (helperSource c world v) (by simpa only [← pc] using related) observed matched aligned latest
      active noReturn (by rfl) initial seed incoming scratch
    rw [cursor] at run
    apply eventually_weaken (historyStep fetch) _ _ _ _ run
    rintro final ⟨ret, result, ready, frame, points, full, returned, matching, cuts, endpoint,
      tail, recorded, frames⟩
    refine ⟨by simpa only [← pc] using ret, (by simp), (by simp), (by simp), ⟨v, projected, rfl, rfl⟩, ?_, (by rw [result]; rfl), ready, ?_, _, points, ?_, full, returned, matching, cuts, endpoint,
      tail, recorded, ?_⟩
    · rw [result]; rfl
    · intro a outside
      exact frame a (fun h => outside (.inr h))
    · intro prior
      rw [focusPeer]
      exact MirrorHistory.peer_null_run_logged prior _
    · intro q member cut a outside
      exact frames q member cut a (fun written => outside (.inr written))
  | some pid =>
    obtain ⟨device, peer, hasDevice, hasPeer, nonnull, field⟩ := related.peer_entry_data c (helperWorld c world v)
      current.machine current.history seen initial pid focusPeer
    have peerPointer : current.machine.data.regs.rdi.toBitVec = c.peers pid := by
      simpa [focusPeer, OwnerWord.pointer] using pointer
    have notNull : current.machine.data.regs.rdi ≠ 0 := by
      intro zero
      apply nonnull
      rw [← peerPointer, zero]
      rfl
    have viewCount : v.count = some peer.refcount := by
      have h := congrArg (fun view : Option View => view.bind (·.count)) projected
      simp only [project, hasDevice, focusPeer, Option.bind_some, Option.pure_def] at h
      change (device.peers.get? pid).map (·.refcount) = v.count at h
      simpa only [hasPeer, Option.map_some] using h.symm
    have acceptedPeer : (peerGetMaybeZero (some pid)).run (helperWorld c world v) = .ok (answer, worldFinal) := by
      simpa only [focusPeer] using accepted
    have bound := PeerMirror.accepted_peer_bound pid _ _ _ device peer hasDevice hasPeer acceptedPeer
    have sourceResult := PeerMirror.accepted_peer_result pid _ _ _ device peer hasDevice hasPeer acceptedPeer
    have run := accepted_nonnull_helper_execution c (helperWorld c world v) device pid peer fetch agree tracePc traceCmp traceByte
      current.machine.data _ (by simpa only [← pc] using abi) notNull answer worldFinal acceptedPeer
      (by simpa only [peerPointer, show BitVec.ofNat 64 Layouts.peer_refcount = 0x420 from rfl] using field)
      ⟨coverage, preempt, v⟩ (512+preempt) state (.inr rfl) mapped separate.push separate.stack separate.metadata separate.preempt
      (by intro nonzero; simpa only [peerPointer, show BitVec.ofNat 64 Layouts.peer_refcount = 0x420 from rfl] using separate.countService pid focusPeer ⟨peer.refcount, viewCount, nonzero⟩)
      (by simpa only [peerPointer, show BitVec.ofNat 64 Layouts.peer_refcount = 0x420 from rfl] using separate.count pid focusPeer) comparison current.history _ raw last
      seen (helperSource c world v) (by simpa only [← pc] using related) observed matched aligned latest
      active noReturn focusPeer peerPointer hasDevice hasPeer (by rfl) initial seed incoming (by
        intro view projection a read written
        have same : view = v := Option.some.inj (projection.symm.trans projected)
        subst view
        rcases written with ⟨nonzero, countByte⟩ | stack
        · exact separate.bucket a read (.inr ⟨⟨peer.refcount, viewCount, nonzero⟩, pid, focusPeer,
            by simpa only [peerPointer, show BitVec.ofNat 64 Layouts.peer_refcount = 0x420 from rfl] using countByte⟩)
        · exact scratch v projected a (by rcases read with head | node; exact .inl head; exact .inr (.inl node)) stack)
      (by
        intro a read written
        rcases written with countByte | stack
        · exact separate.ownerCount a ⟨pid, focusPeer, by simpa only [peerPointer, show BitVec.ofNat 64 Layouts.peer_refcount = 0x420 from rfl] using countByte⟩ read
        · exact scratch v projected a (.inr (.inr (.inl read))) stack)
    rw [cursor] at run
    apply eventually_weaken (historyStep fetch) _ _ _ _ run
    rintro final ⟨ret, scratch, result, ready, frame, points, full, returned, matching, cuts, endpoint,
      tail, recorded, frames⟩
    have outputNeeded : answer.isSome = true → LookupOutputNeeded v := by
      intro live
      refine ⟨peer.refcount, viewCount, ?_, bound⟩
      intro zero
      simp [sourceResult.1, zero] at live
    have mappedOutput : answer.isSome = true → (final.machine.data.dmem.loadInt s.regs.rcx.toBitVec 8).isSome = true := by
      intro live
      have needed := outputNeeded live
      apply output_mapped_after_helper c coverage preempt returnAddress s world v entry current.machine.data
        final.machine.data needed
        (output_mapped_at_helper c coverage preempt returnAddress s world v entry bucket current afterBucket owner savedBefore needed)
        (scratch live)
      intro a outside
      apply frame a
      rintro (⟨nonzero, countByte⟩ | stack)
      · exact outside (.inl (.inr ⟨⟨peer.refcount, viewCount, nonzero⟩, pid, focusPeer,
          by simpa only [peerPointer, show BitVec.ofNat 64 Layouts.peer_refcount = 0x420 from rfl] using countByte⟩))
      · exact outside (.inr stack)
    have projectedFinal := project_peerFinal c (helperWorld c world v) device pid peer v hasDevice hasPeer focusPeer projected
    rw [← sourceResult.2] at projectedFinal
    have sourceFrame : ∃ afterView, project c worldFinal = some afterView ∧ afterView.bucket = v.bucket ∧ afterView.ownerWord = v.ownerWord := by
      refine ⟨_, projectedFinal, ?_, ?_⟩ <;> split <;> rfl
    have alive : decide (final.machine.data.regs.rax ≠ 0) = answer.isSome := by
      rw [result]
      cases answer <;> simp [notNull]
    refine ⟨by simpa only [← pc] using ret, scratch, mappedOutput, outputNeeded, sourceFrame, ?_, alive, ready, ?_, MirrorHistory.peerPoints (helperWorld c world v) peer,
      points, ?_, full, returned, matching, cuts, endpoint, tail, recorded, ?_⟩
    · rw [sourceResult.1] at result ⊢
      by_cases zero : peer.refcount = 0
      · simp only [zero, ite_true, Option.isSome_none, Bool.false_eq_true, ite_false] at result
        rw [result]
        simp [zero, OwnerWord.pointer]
      · simp only [ite_eq_right zero, Option.isSome_some, ite_true] at result
        simpa only [ite_eq_right zero, OwnerWord.pointer, result] using peerPointer
    · intro a outside
      apply frame a
      rintro (⟨nonzero, countByte⟩ | stack)
      · exact outside (.inl (.inr ⟨⟨peer.refcount, viewCount, nonzero⟩, pid, focusPeer,
          by simpa only [peerPointer, show BitVec.ofNat 64 Layouts.peer_refcount = 0x420 from rfl] using countByte⟩))
      · exact outside (.inr stack)
    · intro prior
      rw [focusPeer, sourceResult.1, sourceResult.2]
      exact MirrorHistory.peer_run_logged pid prior (helperWorld c world v) device peer hasDevice hasPeer bound
    · intro q member cut a outside
      apply frames q member cut a
      rintro (⟨nonzero, countByte⟩ | stack)
      · exact outside (.inl (.inr ⟨⟨peer.refcount, viewCount, nonzero⟩, pid, focusPeer,
          by simpa only [peerPointer, show BitVec.ofNat 64 Layouts.peer_refcount = 0x420 from rfl] using countByte⟩))
      · exact outside (.inr stack)

#print axioms helper_from_call
end Binary.LookupRelation
