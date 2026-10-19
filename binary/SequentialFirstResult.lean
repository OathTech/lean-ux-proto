import SequentialResult
import SequentialFirstHelper
namespace Binary.Sequential.First
open Leanux Leanux.WG TrustBase LookupRelation LookupHistory LookupObservation Callback
local instance : Labels := Image.linkedLabels
theorem result_from_helper (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (c : Config)
    (coverage : KcovLayout) (preempt : BitVec 32) (returnAddress : UInt64)
    (s : MachineData) (world : World) (v : View)
    (entry : LookupEntry c coverage preempt returnAddress ⟨s, Image.Lookup.entry⟩ world v)
    (bucket helper current : Executed) (owner : IndexOwner) (focused : c.focus.owner = some owner)
    (before : BeforeHelper c coverage preempt s world v bucket owner helper)
    (answer : Option PeerId) (helperFinal setWorld : World)
    (after : AfterHelper c coverage preempt s world v helper answer helperFinal current)
    (setRun : (owner.setPeerWord answer).run helperFinal = .ok ((), setWorld)) :
    Eventually (guardedHistoryStep fetch (StackGuard s.regs.rsp))
      (AfterResult c coverage preempt s world v owner current answer helperFinal setWorld) current := by
  obtain ⟨callback, _, _, cbStack, cbOwner, _, machine, _⟩ := before
  obtain ⟨ret, scratch, output, needed, ⟨afterView, projected, bucketEq, wordEq⟩, result, alive, ready, frame,
    related⟩ := after
  have pc : current.machine.pc = Image.Lookup.entry+0xba := ret.1
  have location : current.machine.data.regs.rbx.toBitVec = ownerAddress c owner := by
    rw [ret.2.2.1, machine]
    simpa only [peerCalled, Instrumentation.calledState, peerArgument, MachineData.setReg, Reg64s.set, Reg64s.set64] using cbOwner
  have bucketApart : ∀ other, project c helperFinal = some other → ∀ a, LookupBucketBytes c other a →
      ¬InRange (ownerAddress c owner) 8 a := by
    intro other otherProjected a read written
    have same : other = afterView := Option.some.inj (otherProjected.symm.trans projected)
    subst other
    apply entry.dataBucket a _ (.inl ⟨owner, focused, written⟩)
    simpa only [LookupBucketBytes, bucketEq] using read
  have countApart : ∀ a, LookupCountBytes c a → ¬InRange (ownerAddress c owner) 8 a := by
    intro a read written
    exact entry.ownerCount a read ⟨owner, focused, written⟩
  have represented : At c current.machine.data.dmem afterView := by
    obtain ⟨other, projection, physical⟩ := related
    have eq : other = afterView := Option.some.inj (projection.symm.trans projected)
    simpa only [eq] using physical
  have ownerField : OwnerWord.Field c.peers current.machine.data.dmem (ownerAddress c owner) c.focus.peer := by
    have h := represented.2.2.1
    simp only [focused] at h
    obtain ⟨word, wordAt, field⟩ := h
    have original : afterView.ownerWord = some c.focus.peer := by
      rw [wordEq]
      simpa only [EntryFocus, focused] using entry.focus.2
    have eq : word = c.focus.peer := Option.some.inj (wordAt.symm.trans original)
    simpa only [eq] using field
  have run := result_history fetch agree c.peers current.machine.data c.focus.peer
    (by simpa only [location] using ownerField) [⟨current.machine.data, Image.Lookup.entry+0xba⟩]
  have sp : current.machine.data.regs.rsp=s.regs.rsp-40 := by
    rw [ret.2.1,machine]
    change callback.machine.data.regs.rsp-8+8=s.regs.rsp-40
    rw [UInt64.sub_add_cancel,cbStack]
  have guarded := history_guard_suffix (guard := StackGuard s.regs.rsp)
    (historySteps_eventually fetch 4 _ _ run) rfl (by
      rintro t ⟨af,machine,recorded⟩
      refine ⟨_,recorded,?_⟩
      intro q member
      simp only [resultStates,List.dropLast_cons_cons,List.dropLast_singleton,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      all_goals change current.machine.data.regs.rsp≠s.regs.rsp+8
      all_goals rw [sp]; stack_not_return)
  have endpoint := guarded_forget (Q := fun t => ∃ af,t=resultExit current.machine.data af) guarded (fun _ h => ⟨h.choose,h.choose_spec.1⟩)
  have lifted := guarded_lift endpoint current.history
  have cursor : (⟨⟨current.machine.data, Image.Lookup.entry+0xba⟩,current.history⟩ : Executed)=current := by rw [←pc]
  rw [cursor] at lifted
  apply eventually_weaken (guardedHistoryStep fetch (StackGuard s.regs.rsp)) _ _ _ _ lifted
  rintro final ⟨af,machine⟩
  have finalMemory : final.machine.data.dmem = (OwnerWord.stored current.machine.data).dmem := by
    rw [machine]
    rfl
  have memoryFrame : EqualOutside (InRange (ownerAddress c owner) 8) current.machine.data.dmem final.machine.data.dmem := by
    rw [finalMemory, ← location]
    exact OwnerWord.stored_frame _
  have context := LookupCoverage.state_frame ⟨coverage, preempt, v⟩ (512+preempt) _ _ ready _ memoryFrame (by
    intro a read written
    exact entry.dataService a read (.inl ⟨owner, focused, written⟩))
  have oldWord : afterView.ownerWord = some c.focus.peer := by
    rw [wordEq]
    simpa only [EntryFocus, focused] using entry.focus.2
  obtain ⟨next, nextRun, nextView, _, _⟩ := owner_set_project c helperFinal afterView owner c.focus.peer answer projected focused oldWord
  have same : next = setWorld := congrArg Prod.snd (Except.ok.inj (nextRun.symm.trans setRun))
  subst next
  have finalView : project c (LookupMirror.record setWorld .idxPeerAlive answer.isSome) =
      some {afterView with ownerWord := some answer} := by
    simpa only [LookupMirror.record, project_steps] using nextView
  refine ⟨af, ⟨_, finalView, bucketEq⟩, needed, machine, context, ?_, memoryFrame, ?_⟩
  · intro live
    rw [finalMemory]
    exact storeInt_defined _ _ _ _ _ _ (output live)
  · refine ⟨_, finalView, ?_⟩
    exact represented.owner_update owner focused answer memoryFrame (bucketApart afterView projected) countApart (by
      rw [finalMemory, ← location]
      exact OwnerWord.stored_field _ _ _ result)

#print axioms result_from_helper
end Binary.Sequential.First
