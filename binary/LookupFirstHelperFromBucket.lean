import SourceAdapter
import LookupHelperFromBucket
import LookupFirstHelperCall
import PeerFirstStack
namespace Binary.LookupRelation.First
open Leanux Leanux.WG TrustBase LookupHistory LookupObservation PeerCountPhase Callback LookupHistory.First
local instance : Labels := Image.linkedLabels
variable {outer : UInt64}
/-- Selection reaches the actual helper CALL with R at every preceding
    cut. All scratch separation/readiness premises come from LookupEntry.
    The retained callback cursor supplies the helper's stack/read frames. -/
theorem helper_call_from_bucket (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (tracePc : LeafService fetch (.ofNat 0xffffffff810f31f0) (KcovReady .pc) (KcovWrites .pc) (KcovEffect .pc))
    (c : Config) (coverage : KcovLayout) (preempt : BitVec 32) (returnAddress : UInt64)
    (s : MachineData) (world : World) (v : View)
    (entry : LookupEntry c coverage preempt returnAddress ⟨s, Image.Lookup.entry⟩ world v)
    (bucket : Executed) (afterBucket : AfterBucket c world s coverage preempt v bucket)
    (owner : IndexOwner) (focused : c.focus.owner = some owner) :
    Eventually (guardedHistoryStep fetch (StackGuard s.regs.rsp)) (BeforeHelper c coverage preempt s world v bucket owner) bucket := by
  have stateFacts := selected_after_bucket c coverage preempt returnAddress s world v entry bucket afterBucket owner focused
  obtain ⟨head, atHead, _, stop, frame, delta, observed, raw, matched, aligned, related, stable, tags, _⟩ := afterBucket
  obtain ⟨pc, ownerReg, stack, ready, comparison, ownerField, delta', observed', inactive, noReturn, incoming⟩ := stateFacts
  have sameDelta : delta' = delta := List.append_cancel_left (Except.ok.inj (observed'.symm.trans observed))
  subst delta'
  let afterWorld := (LookupSearch.result c.kinds c.query v.bucket [sourceEntry world] world).2
  have projected : project c afterWorld = some v := by
    calc
      _ = project c {world with ambient := {world.ambient with steps := afterWorld.steps}} :=
        congrArg (project c) (LookupSearch.result_world _ _ _ _ _)
      _ = project c world := rfl
      _ = some v := entry.projected
  have scratch : ∀ view, project c afterWorld = some view → ∀ a, Reads c view a →
      ¬scanWrites bucket.machine.data ⟨coverage, preempt, v⟩ a := by
    intro view viewProjection a read written
    have same : view = v := Option.some.inj (viewProjection.symm.trans projected)
    subst view
    apply entry.readsScratch a read
    rcases written with localStack | buffer
    · apply Or.inl
      have loc : bucket.machine.data.regs.rsp.toBitVec-8 = s.regs.rsp.toBitVec-48 := by
        rw [stack, UInt64.toBitVec_sub, BitVec.sub_sub]
        rfl
      rw [loc] at localStack
      have words : LookupStackWords c = 13 := by simp [LookupStackWords, focused]
      change InRange (s.regs.rsp.toBitVec - .ofNat 64 (8*LookupStackWords c)) (8*LookupStackWords c) a
      rw [words]
      apply backwards_range s.regs.rsp.toBitVec 48 104 0 (by decide) a
      obtain ⟨i, hi, eq⟩ := localStack
      exact ⟨i, by omega, eq⟩
    · exact .inr (.inl buffer)
  have callbackRun := selected_callback (outer := s.regs.rsp) fetch agree tracePc c afterWorld bucket pc ⟨coverage, preempt, v⟩
    (512+preempt) (by rw [stack]; constructor <;> stack_not_return) ready ([entryPoint s] ++ delta) delta _ related observed raw matched aligned
    (result_latest c v.bucket [sourceEntry world] world) inactive noReturn scratch
  apply eventually_trans (guardedHistoryStep fetch (StackGuard s.regs.rsp)) _ _ _ callbackRun
  rintro callback ⟨cbPC, cbBX, _, traced, cbObserved, cbMatched, cbAligned, cbRelated⟩
  have cbStack := traced.frame.stack.trans stack
  have cbOwner : callback.machine.data.regs.rbx.toBitVec = ownerAddress c owner := by rw [cbBX]; exact ownerReg
  have wordUnchanged := traced.frame.memory.loadInt (ownerAddress c owner) 8 (by
    intro i hi
    exact scratch v projected _ (.inr (.inr (.inl ⟨owner, focused, i, hi, rfl⟩))))
  have field : callback.machine.data.dmem.loadInt callback.machine.data.regs.rbx.toBitVec 8 =
      some ((OwnerWord.pointer c.peers c.focus.peer).toNat : Int) := by
    rw [cbOwner, ← wordUnchanged]
    exact ownerField
  have cbInitial : scan none callback.history = none := by
    rw [(incoming.trans traced.stable).final none]
    rfl
  have cbScratch : ∀ view, project c afterWorld = some view → ∀ a, Reads c view a →
      ¬InRange (callback.machine.data.regs.rsp.toBitVec-8) 8 a := by
    intro view viewProjection a read written
    apply scratch view viewProjection a read
    left
    simpa only [traced.frame.stack] using written
  have callRun := peer_call_simulation (outer := s.regs.rsp) fetch agree c afterWorld callback.machine.data (by rw [cbStack]; stack_not_return)
    (OwnerWord.pointer c.peers c.focus.peer) callback.history ([entryPoint s] ++ delta) _ field
    traced.frame.ready.mapped (by simpa only [← cbPC] using cbRelated) cbObserved cbMatched cbAligned
    (result_latest c v.bucket [sourceEntry world] world) cbInitial noReturn cbScratch
  have cursor : (⟨⟨callback.machine.data, Image.Lookup.entry+0xb2⟩, callback.history⟩ : Executed) = callback := by rw [← cbPC]
  rw [cursor] at callRun
  apply eventually_weaken (guardedHistoryStep fetch (StackGuard s.regs.rsp)) _ _ _ _ callRun
  rintro t ⟨machine, recorded, callStable, observedFinal, matchedFinal, alignedFinal, relatedFinal⟩
  have argReady := traced.frame.ready.congr
    (after := peerArgument callback.machine.data (OwnerWord.pointer c.peers c.focus.peer)) rfl
    (by simp [peerArgument, MachineData.setReg, Reg64s.set, Reg64s.set64])
  have callState := LookupInstrumentation.called_ready
    (peerArgument callback.machine.data (OwnerWord.pointer c.peers c.focus.peer))
    (Image.Lookup.entry+0xba) Image.PeerGet.entry ⟨coverage, preempt, v⟩ (512+preempt) argReady
  refine ⟨callback, delta, cbPC, cbStack, cbOwner, traced, machine, recorded, ?_, ?_, comparison,
    (incoming.trans traced.stable).trans callStable, observedFinal, matchedFinal, alignedFinal, relatedFinal⟩
  · simpa only [machine, peerCalled] using callState.1
  · simpa only [machine, peerCalled] using callState.2

#print axioms helper_call_from_bucket
end Binary.LookupRelation.First
