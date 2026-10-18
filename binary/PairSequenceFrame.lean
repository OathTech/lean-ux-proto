import PairSequencePre

namespace Binary.Pair.Sequence
open Leanux Leanux.WG TrustBase CommonBitsCoverage Index

/-- Shared heap plus caller frame, output and service writes. Immutable tags
and readable resources are exported separately by `Ready`. -/
def Writes (n : Names) (o : Offsets) (c : Context) (base : MachineState) (a : BitVec 64) : Prop :=
  HeapBytes n o a ∨ LiveStack base 13 a ∨ AllowedipsCoverageWrites c.coverage c.preempt a ∨
    InRange preemptCountAddress 4 a ∨ InRange base.data.regs.rcx.toBitVec 8 a

theorem install_writes (n o c base ra pc arg2 arg3 current) :
    EqualOutside (Writes n o c base) current.data.dmem
      (install n base ra pc arg2 arg3 current).data.dmem := by
  intro a outside
  exact storeInt_frame _ _ _ _ a (fun inside => outside (.inr (.inl (return_live base a inside))))

theorem frame_trans {n o c base first second third}
    (a : EqualOutside (Writes n o c base) first second)
    (b : EqualOutside (Writes n o c base) second third) : EqualOutside (Writes n o c base) first third :=
  fun address outside => (a address outside).trans (b address outside)

theorem stack_small {base : MachineState} {size : Nat} (small : size≤13)
    (a : BitVec 64) (inside : StackBytes base size a) : LiveStack base 13 a := by
  exact stack_live (LookupRelation.backwards_range base.data.regs.rsp.toBitVec (8*size) (8*13) 0
    (by omega) a inside)

theorem external_writes {n o c base ra pc arg2 arg3 current size}
    (small : size≤13) (a : BitVec 64)
    (inside : HeapBytes n o a ∨ External c (install n base ra pc arg2 arg3 current) size a) :
    Writes n o c base a := by
  rcases inside with heap | stack | buffer | preempt
  · exact .inl heap
  · exact .inr (.inl (stack_small small a stack))
  · exact .inr (.inr (.inl buffer))
  · exact .inr (.inr (.inr (.inl preempt)))

theorem mutator_frame {n o c base ra pc arg2 arg3 current size final}
    (small : size≤13)
    (frame : EqualOutside (fun a => HeapBytes n o a ∨
      External c (install n base ra pc arg2 arg3 current) size a)
      (install n base ra pc arg2 arg3 current).data.dmem final) :
    EqualOutside (Writes n o c base) current.data.dmem final := by
  apply frame_trans (install_writes n o c base ra pc arg2 arg3 current)
  exact fun a outside => frame a (fun written => outside (external_writes small a written))

theorem lookup_frame {n o c base ra query kinds current final}
    (frame : EqualOutside (IndexLookup.Writes n o c (install n base ra Image.Lookup.entry (kindMask kinds) query current))
      (install n base ra Image.Lookup.entry (kindMask kinds) query current).data.dmem final) :
    EqualOutside (Writes n o c base) current.data.dmem final := by
  apply frame_trans (install_writes n o c base ra Image.Lookup.entry (kindMask kinds) query current)
  intro a outside
  apply frame a
  rintro (heap | external | output)
  · exact outside (.inl heap)
  · exact outside (external_writes (by omega : 13≤13) a (.inr external))
  · exact outside (.inr (.inr (.inr (.inr output))))

def Interface (n : Names) (ra : UInt64) (entry final : MachineState) (answer : Answer) : Prop :=
  Returned entry final ra ∧ match answer with
  | .lookup value => IndexLookup.Result n entry final value
  | .remove => True
  | .replace value => final.data.regs.rax.toBitVec.setWidth 8=(if value then (1 : BitVec 8) else 0)

#print axioms install_writes
#print axioms mutator_frame
#print axioms lookup_frame
end Binary.Pair.Sequence
