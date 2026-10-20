import PairServiceCall
import PairMappedMemory

namespace Binary.CommonBitsCoverage

/-- Preserve callback resources through a non-callback segment's proved byte
frame. Readability is carried independently of byte values. -/
theorem CallsReady.frame {c : Context} {s t : MachineData} {writes : BitVec 64 → Prop}
    (ready : CallsReady c s) (stack : t.regs.rsp=s.regs.rsp)
    (frame : EqualOutside writes s.dmem t.dmem) (mapped : Pair.MappedLe s.dmem t.dmem)
    (apart : ∀ a, c.bytes a → ¬writes a) : CallsReady c t := by
  exact {
    state := state_frame c _ _ ready.state writes frame apart
    aligned := stack ▸ ready.aligned
    mapped := by rw [stack]; exact mapped _ _ ready.mapped
    pushSeparate := stack ▸ ready.pushSeparate
    returnSeparate := stack ▸ ready.returnSeparate
    metadataSeparate := ready.metadataSeparate
    preemptSeparate := ready.preemptSeparate }

end Binary.CommonBitsCoverage
