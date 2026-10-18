import PairInsertRandomMemory
import PairInsertDrawRegion

namespace Binary.Pair.Insert
open TrustBase CommonBitsCoverage Instrumentation
local instance : Labels := Image.linkedLabels

def ProviderWrites (config : RandomProvider.Config) (c : Context) (initial : MachineState) (a : BitVec 64) : Prop :=
  RandomProvider.PrivateBytes config a ∨ Index.External c initial 135 a

/-- Execute insertion's actual CALL, obtain physical return, then apply only
the independent tape-coupling safety law. The whole caller invariant returns. -/
theorem Core.random_call (fetch : Int64 → Option Decoded) (decoder : IndexInsertDecoderAgreement fetch)
    {n o c initial ra config inputAt shadow s records value rest}
    (physical : RandomReturnContract fetch config)
    (coupling : RandomInputCoupling fetch config c.coverage (c.preempt+512) (codeEntry+0x79).toUInt64 inputAt)
    (facts : FrameFacts n o c initial ra) (provider : ProviderFacts n o c initial ra config)
    (core : Core n o c initial ra .outer shadow s)
    (state : ProviderState config c initial ⟨s,0⟩)
    (input : inputAt s.dmem records) (draw : draw records=.ok (value,rest)) :
    Eventually (instructionStep fetch) (fun t => t.pc=codeEntry+0x79 ∧
      Core n o c initial ra .outer t.data.dmem t.data ∧ ProviderState config c initial t ∧
      inputAt t.data.dmem rest ∧ (drawWord t.data).toNat=value ∧
      Index.StorageFrame n o s.dmem t.data.dmem ∧
      EqualOutside (ProviderWrites config c initial) s.dmem t.data.dmem) ⟨s,codeEntry+0x74⟩ := by
  let ret := codeEntry+0x79
  let target := label "L_ffffffff81375000"
  let entered := calledState s ret target
  have pushFrame : EqualOutside (InRange (Stack.slot initial.data.regs.rsp.toBitVec 7) 8) s.dmem entered.data.dmem := by
    simpa only [entered,calledState,core.call_slot] using
      storeInt_frame s.dmem (s.regs.rsp.toBitVec-8) 8 ret.toBitVec.toInt
  have pushExternal : EqualOutside (Index.External c initial 7) s.dmem entered.data.dmem := by
    intro a outside
    exact pushFrame a (fun h => outside (.inl (Stack.scratch _ 7 7 (by decide) (by decide) a h)))
  have pushedInput : inputAt entered.data.dmem records := coupling.frame _ _ records (by
    intro a privateByte
    exact pushExternal a (provider.private_external a privateByte)) input
  have old : MemoryReady c initial ra (savedWords initial.data) .outer entered.data.dmem := by
    simpa only [entered,calledState,core.call_slot] using core.memory.call_store facts ret.toBitVec
  have calls := core.calls facts
  have physicalCall := call_instruction fetch (codeEntry+0x74) "L_ffffffff81375000"
    (decoder _ _ (by rfl)) s [] calls.mapped
  have callRun := Sequential.forget (Q := fun t => t=calledState s (codeEntry+0x74+5) target)
    (historySteps_eventually fetch 1 _ _ physicalCall) (fun _ h => h.1)
  apply eventually_trans (instructionStep fetch) _ _ _ callRun
  rintro t rfl
  have entryFrame := called_entry s ret target calls.aligned
  have returned := RandomService.return_recorded fetch physical coupling (by rfl)
    (core.random_ready facts provider state ret target) entryFrame pushedInput draw
  apply eventually_weaken (instructionStep fetch) _ _ _ _ returned
  intro t post
  obtain ⟨pc,sp,bx,bp,r12,r13,r14,r15⟩ := returned_caller s ret target t post.returned
  have storage := (Index.external_storage facts.toCallFacts.geometry pushExternal).trans
    (core.random_storage provider ret target post.frame)
  refine ⟨pc,⟨sp.trans core.stack,r12.trans core.table,bp.trans core.owner,
    core.random_memory facts provider ret target old post,?_,?_⟩,
    (state.push provider core ret target).random post,post.remaining,post.valueEqual,storage,?_⟩
  · exact fun _ _ _ _ => rfl
  · exact fun _ _ => rfl
  · intro a outside
    apply (pushExternal a (by
      intro written
      apply outside
      refine .inr ?_
      rcases written with stack | buffer | count
      · exact .inl (Stack.reserve_mono _ 7 135 0 (by decide) a stack)
      · exact .inr (.inl buffer)
      · exact .inr (.inr count))).trans
    apply post.frame a
    intro written
    apply outside
    rcases written with privateByte | stack | buffer
    · exact .inl privateByte
    · refine .inr (.inl ?_)
      unfold RandomStack at stack
      rw [core.random_base] at stack
      obtain ⟨i,hi,eq⟩ := stack
      exact ⟨i,by omega,eq⟩
    · exact .inr (.inr (.inl ⟨.inr buffer.1,buffer.2⟩))

#print axioms Core.random_call
end Binary.Pair.Insert
