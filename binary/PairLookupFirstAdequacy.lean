import SourceAdapter
import PairLookupAdequacy
import SequentialFirstLookup
namespace Binary.Pair.IndexLookup.First
open Leanux Leanux.WG TrustBase LookupRelation CommonBitsCoverage Index Callback
local instance : Labels := Image.linkedLabels
set_option maxRecDepth 2048
/-- Complete index lookup under the same tested reconstruction as removal
and replacement. The old focused relation and precondition are conclusions
of executable checks. Source histories are not interface observations. -/
theorem lookup_checked (fetch : Int64 → Option Decoded)
    (decoder : AnchoredDecoderAgreement fetch) (tracePc : LeafService fetch (.ofNat 0xffffffff810f3100) (KcovReady .pc) (KcovWrites .pc) (KcovEffect .pc))
    (traceCmp4 : LeafService fetch (.ofNat 0xffffffff810f3e80) (KcovReady .cmp4) (KcovWrites .cmp4) (KcovEffect .cmp4)) (traceConstCmp4 : LeafService fetch (.ofNat 0xffffffff810f3f00) (KcovReady .constCmp4) (KcovWrites .constCmp4) (KcovEffect .constCmp4))
    (traceConstCmp1 : LeafService fetch (.ofNat 0xffffffff810f3ec0) (KcovReady .constCmp1) (KcovWrites .constCmp1) (KcovEffect .constCmp1)) (bhEnable : LeafService fetch (.ofNat 0xffffffff810732c0) BhEnableReady (fun _ => InRange preemptCountAddress 4) (fun before after => ∀ old : BitVec 32, before.data.dmem.loadInt preemptCountAddress 4 = some (old.toNat : Int) → after.data.dmem.loadInt preemptCountAddress 4 = some ((old-before.data.regs.get (.low .rsi .W32)).toNat : Int)))
    {n o coverage initial w query kinds ra answer finalWorld}
    (checked : Pre n o coverage initial w query kinds ra)
    (accepted : (Source.indexLookup kinds query).run w=.ok (answer,finalWorld)) :
    Eventually (guardedStep fetch (StackGuard initial.data.regs.rsp)) (Post n o coverage initial ra answer finalWorld) initial := by
  obtain ⟨d,facts⟩ := pre_facts checked
  let c := callConfig n w d query kinds
  let v := callView c d
  obtain ⟨finalDevice,deviceFinal,source,allowed⟩ := lookup_source_frame facts accepted
  have run := Sequential.First.lookup_simulation fetch decoder tracePc traceCmp4 traceConstCmp4 traceConstCmp1 bhEnable
    c coverage.coverage coverage.preempt ra initial w ⟨v,facts.entry⟩ answer finalWorld accepted
  apply eventually_weaken (guardedStep fetch (StackGuard initial.data.regs.rsp)) _ _ _ _ run
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
end Binary.Pair.IndexLookup.First
