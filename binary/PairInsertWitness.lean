import PairInsertWitnessProvider
import PairInsertProviderComplete

namespace Binary.Pair.Insert.Witness
open Leanux Leanux.WG TrustBase Index
local instance : Labels := Image.linkedLabels
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

private instance [DecidableEq α] (x : Except ε α) (v : α) : Decidable (x=.ok v) :=
  match x with
  | .error e => .isFalse (by intro h; cases h)
  | .ok actual => decidable_of_iff (actual=v) (by simp)

theorem arguments (m : DataMem) : ((frameState m).pc.toBitVec.toNat==Insert.entry &&
    (frameState m).data.regs.rdi.toNat==names.table && (frameState m).data.regs.rsi.toNat==0x700000)=true := by
  simp only [frameState,Remove.Witness.frameState]
  decide +kernel

theorem boundary_for_memory (linked : Bool) (m : DataMem)
    (reads : ∀ a size, m.loadBytes a size=byteList linked a size)
    (asserted : Remove.assertAt names offsets m (world linked)=.ok ())
    (frame : Index.callFrameCheck names offsets context (frameState m) (.ofNat stopAddr) 7=.ok ()) :
    callBoundary names offsets context (frameState m) (world linked) (.keypair 0) (.ofNat stopAddr)=.ok () :=
  @boundary_of_parts names offsets context (frameState m) (world linked)
    (.keypair 0) (.ofNat stopAddr) 0x700000 asserted (by decide +kernel) (arguments m)
    (resident_for_memory linked m reads)
    ⟨Index.callFrameCheck_sound frame,nested_for_memory linked m reads,by decide,
      fun impossible => False.elim ((by decide : ¬LookupPendingRead (context.preempt+512)) impossible),
      fun impossible => False.elim ((by decide : ¬LookupPendingRead (context.preempt+512)) impossible)⟩ rfl

theorem boundary (linked : Bool) :
    callBoundary names offsets context (state linked) (world linked) (.keypair 0) (.ofNat stopAddr)=.ok () :=
  boundary_for_memory linked (memory linked) (memory_load linked) (asserted linked) (call_frame linked false)

theorem private_check (linked : Bool) :
    RandomProvider.check config 0x800000 false (memory linked)=.ok () :=
  private_for_memory linked (memory linked) (memory_load linked)

theorem provider_for_memory (linked : Bool) (m : DataMem)
    (reads : ∀ a size, m.loadBytes a size=byteList linked a size)
    (wide : Index.callFrameCheck names offsets context (frameState m) (.ofNat stopAddr) 135=.ok ()) :
    providerCheck names offsets context (frameState m) (.ofNat stopAddr) config=.ok () := by
  apply ProviderFacts.checked
  refine ⟨Index.callFrameCheck_sound wide,rfl,?_,?_,private_for_memory linked m reads,?_,?_⟩
  · exact (by decide +kernel : (512 : BitVec 64)[10]=false)
  · intro impossible
    exact False.elim ((by decide : ¬(CommonBitsCoverage.Context.mk context.coverage (context.preempt+512)).Needed) impossible)
  all_goals
    simp only [providerProtected,Index.callStack,frameState,Remove.Witness.frameState]
    decide +kernel

theorem provider (linked : Bool) :
    providerCheck names offsets context (state linked) (.ofNat stopAddr) config=.ok () :=
  provider_for_memory linked (memory linked) (memory_load linked) (call_frame linked true)

theorem check (linked : Bool) : Pre names offsets context (state linked) (world linked)
    (.keypair 0) (.ofNat stopAddr) config := ⟨boundary linked,provider linked⟩

#print axioms check
end Binary.Pair.Insert.Witness
