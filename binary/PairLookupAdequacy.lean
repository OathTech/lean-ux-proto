import PairLookupOwnership
import PairLookupReadiness
import PairIndexKinds

namespace Binary.Pair.IndexLookup
open Leanux Leanux.WG TrustBase LookupRelation CommonBitsCoverage Index
local instance : Labels := Image.linkedLabels
set_option maxRecDepth 2048

def Result (n : Names) (initial final : MachineState) (answer : Option (IndexOwner×PeerId)) : Prop :=
  match answer with
  | none => final.data.regs.rax=0
  | some (owner,peer) => final.data.regs.rax.toBitVec=physicalOwner n owner ∧
      final.data.dmem.loadInt initial.data.regs.rcx.toBitVec 8=some ((peerPointer n peer).toNat : Int)

def Writes (n : Names) (o : Offsets) (coverage : Context) (initial : MachineState) (a : BitVec 64) : Prop :=
  HeapBytes n o a ∨ External coverage initial 13 a ∨ InRange initial.data.regs.rcx.toBitVec 8 a

def Post (n : Names) (o : Offsets) (coverage : Context) (initial : MachineState)
    (ra : UInt64) (answer : Option (IndexOwner×PeerId)) (finalWorld : World) (final : MachineState) : Prop :=
  Returned initial final ra ∧ Result n initial final answer ∧
  (∃ d, finalWorld.k.wg=some d ∧ Corresponds n o final.data.dmem d ∧
    Remove.ownership n o final.data.dmem=.ok (Remove.targetOwnership d)) ∧
  (∀ b, (phase coverage b).CoverageAt final.data.dmem) ∧
  load32 final.data.dmem preemptCountAddress=some coverage.preempt ∧
  (LookupPendingRead coverage.preempt → final.data.dmem.loadInt softirqPendingAddress 2=some 0) ∧
  EqualOutside (Writes n o coverage initial) initial.data.dmem final.data.dmem ∧ KindFrame n o initial.data.dmem final.data.dmem

theorem write_frame {n o coverage s w d query kinds ra after}
    (facts : CallFacts n o coverage s w d query kinds ra)
    (frame : EqualOutside (LookupWrites (callConfig n w d query kinds) coverage.coverage coverage.preempt s.data
      (callView (callConfig n w d query kinds) d)) s.data.dmem after) :
    EqualOutside (Writes n o coverage s) s.data.dmem after := by
  intro a outside
  apply frame a
  rintro (stack | buffer | preempt | data | ⟨_,output⟩)
  · apply outside (.inr (.inl (.inl ?_)))
    have bound : LookupStackWords (callConfig n w d query kinds)≤13 := by unfold LookupStackWords; split <;> decide
    exact backwards_range s.data.regs.rsp.toBitVec (8*LookupStackWords (callConfig n w d query kinds)) (8*13) 0
      (by omega) a stack
  · exact outside (.inr (.inl (.inr (.inl (coverage_writes buffer)))))
  · exact outside (.inr (.inl (.inr (.inr preempt))))
  · exact outside (.inl (data_heap facts.related facts.names a data))
  · exact outside (.inr (.inr output))

/-- Complete index lookup under the same tested reconstruction as removal
and replacement. The old focused relation and precondition are conclusions
of executable checks. Source histories are not interface observations. -/
theorem lookup_checked (fetch : Int64 → Option Decoded)
    (decoder : AnchoredDecoderAgreement fetch) (tracePc : TracePcContract fetch)
    (traceCmp4 : TraceCmp4Contract fetch) (traceConstCmp4 : TraceConstCmp4Contract fetch)
    (traceConstCmp1 : TraceConstCmp1Contract fetch) (bhEnable : BhEnableContract fetch)
    {n o coverage initial w query kinds ra answer finalWorld}
    (checked : Pre n o coverage initial w query kinds ra)
    (accepted : (WG.indexLookup kinds query).run w=.ok (answer,finalWorld)) :
    Eventually (instructionStep fetch) (Post n o coverage initial ra answer finalWorld) initial := by
  obtain ⟨d,facts⟩ := pre_facts checked
  let c := callConfig n w d query kinds
  let v := callView c d
  obtain ⟨finalDevice,deviceFinal,source,allowed⟩ := lookup_source_frame facts accepted
  have run := Sequential.lookup_simulation fetch decoder tracePc traceCmp4 traceConstCmp4 traceConstCmp1 bhEnable
    c coverage.coverage coverage.preempt ra initial w ⟨v,facts.entry⟩ answer finalWorld accepted
  apply eventually_weaken (instructionStep fetch) _ _ _ _ run
  rintro final ⟨returned,result,related,oldView,oldEntry,frame,covered,preempt,pending⟩
  have projected : project c w=some v := by unfold project; rw [facts.device]; rfl
  have same : oldView=v := Option.some.inj (oldEntry.projected.symm.trans projected)
  subst oldView
  obtain ⟨newView,newProjected,physical⟩ := related
  have projectedFinal : project c finalWorld=some (callView c finalDevice) := by
    unfold project; rw [deviceFinal]; rfl
  have same : newView=callView c finalDevice := Option.some.inj (newProjected.symm.trans projectedFinal)
  subst newView
  refine ⟨returned,result,⟨finalDevice,deviceFinal,reconstruct_after facts source allowed physical frame,
    ownership_after facts source frame⟩,coverage_after facts covered frame,preempt,pending,write_frame facts frame,?_⟩
  intro owner base named path
  have shape := facts.shape_frame frame
  have member : (base+8,24) ∈ shapeSpans n o :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(owner,base),named,rfl⟩)
  have read := shape.word member 16 4 (by omega) path
  have layout := (validate_basic (reconstruct_components facts.related).1).1
  simpa only [layout.kind,Nat.add_assoc] using read.symm

#print axioms lookup_checked
end Binary.Pair.IndexLookup
