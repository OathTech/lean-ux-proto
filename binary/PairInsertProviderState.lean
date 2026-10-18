import PairInsertProvider

namespace Binary.Pair.Insert
open TrustBase CommonBitsCoverage
local instance : Labels := Image.linkedLabels

/-- Private readiness and ISA-preserved physical resources. Reconstruction
does not contain any of these clauses or the external input interpretation. -/
structure ProviderState (config : RandomProvider.Config) (c : Context)
    (initial s : MachineState) : Prop where
  privateCheck : RandomProvider.check config c.coverage.task.toNat
    (RandomRecordingActive c.coverage (c.preempt+512)) s.data.dmem=.ok ()
  privilege : s.data.system.cpl=0
  direction : s.data.system.bits[10]=false
  mapped : ∀ a n, (initial.data.dmem.loadInt a n).isSome=true → (s.data.dmem.loadInt a n).isSome=true

theorem ProviderState.initial {n o c initial ra config}
    (facts : ProviderFacts n o c initial ra config) : ProviderState config c initial initial :=
  ⟨facts.privateCheck,facts.privilege,facts.direction,fun _ _ h => h⟩

theorem ProviderState.at_pc {config c initial s} (state : ProviderState config c initial s) (pc : Int64) :
    ProviderState config c initial ⟨s.data,pc⟩ :=
  ⟨state.privateCheck,state.privilege,state.direction,state.mapped⟩

/-- Ordinary insertion regions preserve private bytes. Mapping and system
mode are obtained from the actual execution, without per-region assumptions. -/
theorem ProviderState.follow (fetch : Int64 → Option Decoded) {config c initial s post}
    (state : ProviderState config c initial s) (run : Eventually (instructionStep fetch) post s)
    (frame : ∀ t, post t → ∀ a, RandomProvider.PrivateBytes config a →
      s.data.dmem.get? a=t.data.dmem.get? a) :
    Eventually (instructionStep fetch) (fun t => post t ∧ ProviderState config c initial t) s := by
  have mapped := MemoryInvariant.eventually_mapped fetch run
  have mode := SystemInvariant.eventually_mode fetch mapped
  apply eventually_weaken (instructionStep fetch) _ _ _ _ mode
  rintro t ⟨⟨result,mapped⟩,privilege,direction⟩
  refine ⟨result,?_,privilege.trans state.privilege,direction.trans state.direction,
    fun a n h => mapped a n (state.mapped a n h)⟩
  rw [←RandomProvider.check_frame (frame t result)]
  exact state.privateCheck

theorem ProviderState.random {config c initial s inputAt ra value rest t}
    (state : ProviderState config c initial s)
    (post : RandomService.Post config c.coverage (c.preempt+512) inputAt s ra value rest t) :
    ProviderState config c initial t :=
  ⟨post.privateCheck,post.privilege.trans state.privilege,post.direction.trans state.direction,
    fun a n h => post.mapped a n (state.mapped a n h)⟩

/-- The original wide reservation remains mapped after arbitrary stores. -/
theorem ProviderState.stack {n o c initial ra config s}
    (facts : ProviderFacts n o c initial ra config) (state : ProviderState config c initial s) :
    ∀ offset<1080, (s.data.dmem.get? (Stack.slot initial.data.regs.rsp.toBitVec 135+.ofNat 64 offset)).isSome=true := by
  apply Stack.bytes_mapped s.data.dmem initial.data.regs.rsp.toBitVec 135
  intro i bound
  apply state.mapped
  simpa only [Stack.slot,Nat.mul_comm] using facts.wide.stack i bound

#print axioms ProviderState.follow
#print axioms ProviderState.random
#print axioms ProviderState.stack
end Binary.Pair.Insert
