import SourceAdapter
import SequentialPeer
import SequentialRelation
import LookupHelperPrepared

namespace Binary.Sequential
open Leanux Leanux.WG TrustBase LookupRelation LookupHistory LookupObservation
local instance : Labels := Image.linkedLabels

def AfterHelper (c : Config) (coverage : KcovLayout) (preempt : BitVec 32)
    (s : MachineData) (_world : World) (v : View) (current : Executed)
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
      Related c final.machine worldFinal

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
    (accepted : (Source.peerGetMaybeZero c.focus.peer).run (helperWorld c world v) = .ok (answer, worldFinal)) :
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
  have projected : project c (helperWorld c world v) = some v := by
    calc
      _ = project c {world with ambient := {world.ambient with steps := (helperWorld c world v).steps}} :=
        congrArg (project c) (LookupSearch.result_world _ _ _ _ _)
      _ = project c world := rfl
      _ = some v := entry.projected
  let seen := ([entryPoint s] ++ delta) ++ [call "wg_peer_get_maybe_zero" current.machine]
  have initial : PeerCountPhase.scan none current.history = none := by rw [stable.final none]; rfl
  have represented : At c current.machine.data.dmem v := by
    obtain ⟨view, projection, physical⟩ := related.2.1
    have eq : view = v := Option.some.inj (projection.symm.trans projected)
    subst view
    exact of_physical physical (by simp [countPhase, initial])
      (by simp [ownerPending, pc, Image.Lookup.entry, Image.PeerGet.entry])
  cases focusPeer : c.focus.peer with
  | none =>
    have null : current.machine.data.regs.rdi = 0 := by
      apply UInt64.toBitVec_inj.mp
      simpa [focusPeer, OwnerWord.pointer] using pointer
    rw [focusPeer, PeerMirror.peer_null_run] at accepted
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj accepted.symm)
    have physical := PeerGet.null_entry_history fetch agree tracePc current.machine.data _
      (by simpa only [← pc] using abi) null ⟨coverage, preempt, v⟩ (512+preempt) state (.inr rfl) mapped
      separate.push separate.stack separate.metadata separate.preempt
      0 [⟨current.machine.data, Image.PeerGet.entry⟩] [] rfl rfl
    have endpoint : Eventually (instructionStep fetch) (fun final =>
        Returned ⟨current.machine.data, Image.PeerGet.entry⟩ final (Image.Lookup.entry+0xba).toUInt64 ∧
        final.data.regs.rax = 0 ∧
        LookupCoverage.Context.At ⟨coverage, preempt, v⟩ (512+preempt) final.data.dmem ∧
        EqualOutside (PeerGet.entryWrites current.machine.data ⟨coverage, preempt, v⟩)
          current.machine.data.dmem final.data.dmem) ⟨current.machine.data, Image.PeerGet.entry⟩ :=
      forget physical (fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)
    have run := history_lift fetch _ _ endpoint current.history
    have cursor : (⟨⟨current.machine.data, Image.PeerGet.entry⟩, current.history⟩ : Executed) = current := by rw [← pc]
    rw [cursor] at run
    apply eventually_weaken (historyStep fetch) _ _ _ _ run
    rintro final ⟨ret, result, ready, frame⟩
    refine ⟨by simpa only [← pc] using ret, (by simp), (by simp), (by simp), ⟨v, projected, rfl, rfl⟩,
      ?_, (by rw [result]; rfl), ready, ?_, ?_⟩
    · rw [result]; rfl
    · intro a outside
      exact frame a (fun h => outside (.inr h))
    · exact ⟨v, projected, represented.frame frame separate.reads⟩
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
    have acceptedPeer : (Source.peerGetMaybeZero (some pid)).run (helperWorld c world v) = .ok (answer, worldFinal) := by
      simpa only [focusPeer] using accepted
    have bound := PeerMirror.accepted_peer_bound pid _ _ _ device peer hasDevice hasPeer acceptedPeer
    have sourceResult := PeerMirror.accepted_peer_result pid _ _ _ device peer hasDevice hasPeer acceptedPeer
    have physical := peer_nonnull (helperWorld c world v) device pid peer fetch agree tracePc traceCmp traceByte
      current.machine.data _ (by simpa only [← pc] using abi) notNull answer worldFinal acceptedPeer
      (by simpa only [peerPointer, show BitVec.ofNat 64 Layouts.peer_refcount = 0x420 from rfl] using field)
      ⟨coverage, preempt, v⟩ (512+preempt) state (.inr rfl) mapped separate.push separate.stack separate.metadata separate.preempt
      (by intro nonzero; simpa only [peerPointer, show BitVec.ofNat 64 Layouts.peer_refcount = 0x420 from rfl] using separate.countService pid focusPeer ⟨peer.refcount, viewCount, nonzero⟩)
      (by simpa only [peerPointer, show BitVec.ofNat 64 Layouts.peer_refcount = 0x420 from rfl] using separate.count pid focusPeer) comparison hasDevice hasPeer
    have run := history_lift fetch _ _ physical current.history
    have cursor : (⟨⟨current.machine.data, Image.PeerGet.entry⟩, current.history⟩ : Executed) = current := by rw [← pc]
    rw [cursor] at run
    apply eventually_weaken (historyStep fetch) _ _ _ _ run
    rintro final ⟨ret, scratch, result, ready, finalCount, frame⟩
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
    have updated := represented.count_update pid focusPeer
      (if peer.refcount = 0 then 0 else peer.refcount+1) frame (by
        intro a read written
        rcases written with ⟨nonzero, countByte⟩ | stack
        · exact separate.bucket a read (.inr ⟨⟨peer.refcount, viewCount, nonzero⟩, pid, focusPeer,
            by simpa only [peerPointer, show BitVec.ofNat 64 Layouts.peer_refcount = 0x420 from rfl] using countByte⟩)
        · exact separate.reads a (by rcases read with head | node; exact .inl head; exact .inr (.inl node)) stack) (by
        intro a read written
        rcases written with countByte | stack
        · exact separate.ownerCount a ⟨pid, focusPeer,
            by simpa only [peerPointer, show BitVec.ofNat 64 Layouts.peer_refcount = 0x420 from rfl] using countByte.2⟩ read
        · exact separate.reads a (.inr (.inr (.inl read))) stack) (by
          simpa only [peerPointer, show BitVec.ofNat 64 Layouts.peer_refcount = 0x420 from rfl] using finalCount)
    have relatedFinal : Related c final.machine worldFinal := by
      refine ⟨_, projectedFinal, ?_⟩
      by_cases zero : peer.refcount = 0
      · have viewEq : {v with count := some 0} = v := by
          cases v
          simp_all
        simpa only [zero, ite_true, viewEq] using updated
      · simpa only [ite_eq_right zero] using updated
    refine ⟨by simpa only [← pc] using ret, scratch, mappedOutput, outputNeeded, sourceFrame,
      ?_, alive, ready, ?_, relatedFinal⟩
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

#print axioms helper_from_call
end Binary.Sequential
