import PairInsertRandomCall
import PairInsertDrawFrame

namespace Binary.Pair.Insert
open Leanux Leanux.WG TrustBase CommonBitsCoverage Index
local instance : Labels := Image.linkedLabels

/-- Footprint for the complete insertion, including its private random service. -/
def Writes (n : Names) (o : Offsets) (config : RandomProvider.Config) (c : Context)
    (initial : MachineState) (a : BitVec 64) : Prop :=
  HeapBytes n o a ∨ ProviderWrites config c initial a

theorem external_writes {n o config c initial a} (written : External c initial 7 a) :
    Writes n o config c initial a := by
  refine .inr (.inr ?_)
  rcases written with stack | buffer | count
  · exact .inl (Stack.reserve_mono _ 7 135 0 (by decide) a stack)
  · exact .inr (.inl buffer)
  · exact .inr (.inr count)

theorem ordinary_frame {n o config c initial before after}
    (frame : EqualOutside (fun a => HeapBytes n o a ∨ External c initial 7 a) before after) :
    EqualOutside (Writes n o config c initial) before after := by
  intro a outside
  exact frame a (fun written => outside (written.elim Or.inl external_writes))

/-- Retry boundary through the trace callback and actual random CALL. The
recorded value and its remaining tape are obtained from the named coupling. -/
theorem retry_draw (fetch : Int64 → Option Decoded) (decoder : IndexInsertDecoderAgreement fetch)
    (trace : TracePcContract fetch) {n o c initial ra config inputAt s d owner base records value rest}
    (physical : RandomReturnContract fetch config)
    (coupling : RandomInputCoupling fetch config c.coverage (c.preempt+512) (codeEntry+0x79).toUInt64 inputAt)
    (facts : FrameFacts n o c initial ra) (provider : ProviderFacts n o c initial ra config)
    (core : Core n o c initial ra .outer s.dmem s)
    (ready : RetryData n o s.dmem d owner base)
    (state : ProviderState config c initial ⟨s,0⟩)
    (input : inputAt s.dmem records) (decoded : draw records=.ok (value,rest)) :
    Eventually (instructionStep fetch) (fun t => t.pc=codeEntry+0x79 ∧
      Core n o c initial ra .outer t.data.dmem t.data ∧
      RetryData n o t.data.dmem d owner base ∧ ProviderState config c initial t ∧
      inputAt t.data.dmem rest ∧ (drawWord t.data).toNat=value ∧
      EqualOutside (Writes n o config c initial) s.dmem t.data.dmem ∧
      KindFrame n o s.dmem t.data.dmem) ⟨s,codeEntry+0x6f⟩ := by
  have callback := core.callback fetch (codeEntry+0x6f) "L_ffffffff810f31f0" trace
    (decoder _ _ (by rfl)) facts
  have prepared := (state.at_pc (codeEntry+0x6f)).follow fetch callback (by
    intro t post a privateByte
    exact post.2.1.outside a (provider.private_external a privateByte))
  apply eventually_trans (instructionStep fetch) _ _ _ prepared
  rintro called ⟨⟨pc,core,_,_,_,_⟩,state⟩
  have input : inputAt called.data.dmem records := coupling.frame _ _ records
    (fun a privateByte => core.outside a (provider.private_external a privateByte)) input
  have random := core.random_call fetch decoder physical coupling facts provider
    (state.at_pc 0) input decoded
  apply eventually_weaken (instructionStep fetch) _ _ _ _ (at_pc pc random)
  rintro t ⟨pc,core',state,input,value,frame,outside⟩
  have storage := core.frame.trans frame
  refine ⟨pc,core',ready.frame storage,state,input,value,?_,storage.kinds ?_⟩
  · intro a no
    exact (core.outside a (fun h => no (external_writes h))).trans
      (outside a (fun h => no (.inr h)))
  · exact (validate_basic (reconstruct_components ready.related).1).1

#print axioms retry_draw
end Binary.Pair.Insert
