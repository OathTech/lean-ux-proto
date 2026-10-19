import Leanux.Kernel.Defs
import Leanux.Seccomp.Engine

/-!
# The bridge: stream U's `SeccompM` over the mirror monad

seccomp stream V (docs/2026-10-12-seccomp-design.md; stream U's deviation 1).
The checker, the translation and the engine (`Leanux/Seccomp/Classic.lean`,
`Translate.lean`, `Engine.lean`) are written over the `SeccompM` typeclass
with their own decision table (`SDecision`) and allocation sites
(`SAllocSite`), because the shared `Decision` enumeration cannot be extended
from a leaf module. This file is the one instance over `Seccomp.M` (the state split: the
filter store over the task store over the ambient monad):

- each `SDecision` maps to its `Decision` constructor
  (`SDecision.toDecision`, `Leanux/Kernel/Decision.lean`), whose info,
  comparison and repeatable entries delegate to U's table;
- each `SAllocSite` maps to its `AllocSite` (`hiddenAlloc`);
- the kind-309 records of the translated program are read in stream W's
  order, the eBPF length first and then one word per instruction
  (`HiddenSite.bpfProgInsn`); the translation asks for the instructions
  first and the length last, so the bridge reads the length at the first
  request and holds it in `SeccompWorld.translatedLen`;
- a repeatable decision's (decision, outcome, operands) pair is emitted
  once per operation (design 4.2, 4.5): `SeccompWorld.emitted` keeps the keys.

Nothing here absorbs a failure: every stop the walkers raise is the mirror's
own `Stop`.

The two instruction and program types are converted at this seam: stream U's
leaf modules define `Leanux.Seccomp.SockFilter`, `BpfInsn` and `BpfProg`
(offsets and immediates as `Int`), the interface commit defines the kernel
state's `Leanux.SockFilter`, `BpfInsn` (`Int16`, `Int32`) and `BpfProg`.
-/

namespace Leanux.Seccomp

/-- The allocation site of one of stream U's, in the shared table
    (design 3.1, sites 2-11). -/
def SAllocSite.toAllocSite : SAllocSite → AllocSite
  | .bpfProgAllocImage => .vmallocBpfProg
  | .bpfProgAllocAux => .kzallocBpfAux
  | .bpfProgAllocActive => .percpuBpfActive
  | .bpfProgAllocStats => .percpuBpfStats
  | .kmallocOrigFkprog => .kmallocOrigFprog
  | .kmemdupOrigFilter => .kmemdupOrigFilter
  | .kmallocArrayMasks => .kmallocArrayMasks
  | .kmemdupArrayOldProg => .kmemdupOldProg
  | .bpfProgReallocImage => .vmallocBpfProgRealloc
  | .kcallocAddrs => .kcallocAddrs

/-- The dedup key of a repeatable step: the decision, its outcome and its
    operands. -/
private def stepKey (d : Decision) (o : Bool) (ops : Option (Int × Int)) : String :=
  let o' := if o then "1" else "0"
  match ops with
  | some (a, b) => s!"{d.ctorIdx}:{o'}:{a},{b}"
  | none => s!"{d.ctorIdx}:{o'}"

/-- Record a step as `Leanux.branch`/`branchCmp` do, except that a
    repeatable decision's pair is emitted once per operation (design 4.2). -/
def emit (d : Decision) (o : Bool) (ops : Option (Int × Int)) : M Unit := do
  if d.repeatable then
    let key := stepKey d o ops
    let w ← get
    if w.emitted.contains key then return
    set { w with emitted := w.emitted.insert key }
  modifyAmbient fun a => { a with steps := a.steps.push { decision := d, outcome := o, operands := ops, netRx := a.netRxSection } }

/-- A C decision point of the seccomp paths (the kernel's `Decision`), with
    the once-per-operation rule for the repeatable ones. -/
def kbranch (d : Decision) (o : Bool) : M Bool := do
  emit d o none
  return o

/-- A C value comparison of the seccomp paths, likewise. -/
def kbranchCmp (d : Decision) (o : Bool) (a b : Int) : M Bool := do
  emit d o (some (a, b))
  return o

/-- A flag test `(x & mask) != 0`, reported as the compiler compares it: the
    masked value against zero (`Leanux/FS/File.lean`'s convention; measured
    for every single-flag test of the seccomp paths). -/
def kflag (d : Decision) (x mask : UInt32) : M Bool :=
  kbranchCmp d ((x &&& mask) != 0) (x &&& mask).toNat 0

instance : SeccompM M where
  branch d o := kbranch d.toDecision o
  branchCmp d o a b := kbranchCmp d.toDecision o a b
  alloc s := hiddenAlloc s.toAllocSite
  translatedInsn := do
    if (← getAmbient).hidden.isNone then return none   -- no records: the domain filter
    if (← get).translatedLen.isNone then
      -- stream W's order: the length record precedes the instructions
      let n ← hiddenU64 .bpfProgInsn
      modify fun w => { w with translatedLen := some n }
    return some (← hiddenU64 .bpfProgInsn)
  translatedLen := do
    if (← getAmbient).hidden.isNone then return none
    let w ← get
    match w.translatedLen with
    | some n =>
      set { w with translatedLen := none }
      return some n
    | none =>
      -- no instruction was asked for first: a translation never emits zero
      -- instructions (the prologue alone is three), so this is a mirror defect
      _root_.Leanux.invariant "the translated length was asked for before any instruction"
  recordMismatch what := throw (.hidden what)
  unsupported what := _root_.Leanux.unsupported what
  invariant what := _root_.Leanux.invariant what

/-! ## The two program representations -/

instance : Inhabited _root_.Leanux.SockFilter := ⟨⟨0, 0, 0, 0⟩⟩

def SockFilter.ofKernel (f : _root_.Leanux.SockFilter) : SockFilter := ⟨f.code, f.jt, f.jf, f.k⟩
def SockFilter.toKernel (f : SockFilter) : _root_.Leanux.SockFilter := ⟨f.code, f.jt, f.jf, f.k⟩

def BpfInsn.toKernel (i : BpfInsn) : _root_.Leanux.BpfInsn :=
  { code := i.code, dst := i.dst, src := i.src, off := Int16.ofInt i.off, imm := Int32.ofInt i.imm }
def BpfInsn.ofKernel (i : _root_.Leanux.BpfInsn) : BpfInsn :=
  { code := i.code, dst := i.dst, src := i.src, off := i.off.toInt, imm := i.imm.toInt }

/-- The translated program as the kernel state holds it (`SeccompFilter.prog`). -/
def BpfProg.toKernel (p : BpfProg) : _root_.Leanux.BpfProg :=
  { insns := p.insns.map BpfInsn.toKernel, stackDepth := p.stackDepth, len := p.len }

/-- A filter's program as the engine runs it (with `orig_prog`, which the
    engine does not read). -/
def progOfFilter (f : SeccompFilter) : BpfProg :=
  { insns := f.prog.insns.map BpfInsn.ofKernel, len := f.prog.len, stackDepth := f.prog.stackDepth,
    origProg := f.origProg.map SockFilter.ofKernel }

end Leanux.Seccomp
