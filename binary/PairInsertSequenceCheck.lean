import SourceAdapter
import PairSequenceCheck
import PairInsertProvider

namespace Binary.Pair.InsertSequence
open Leanux Leanux.WG TrustBase CommonBitsCoverage

/-- Extend the completed subsystem without changing its existing statements. -/
inductive Call where
  | existing (call : Sequence.Call)
  | insert (owner : IndexOwner)
  deriving Repr

inductive Answer where
  | existing (answer : Sequence.Answer)
  | insert (index : Nat)
  deriving Repr, BEq

def source : Call → M Answer
  | .existing call => return .existing (← Sequence.source call)
  | .insert owner => return .insert (← Source.indexInsert owner)

def program : List Call → M (List Answer)
  | [] => pure []
  | call::rest => do return (← source call)::(← program rest)

def prepare (n : Names) (base : MachineState) (ra : UInt64) (call : Call)
    (current : MachineState) : Except String MachineState := do
  match call with
  | .existing call => Sequence.prepare n base ra call current
  | .insert owner => return Sequence.install n base ra (.ofNat Insert.entry) (← addressOf n owner) 0 current

def Admissible (n : Names) (call : Call) (w : World) : Prop :=
  match call with
  | .existing call => Sequence.Admissible n call w
  | .insert owner => ∃ a, addressOf n owner=.ok a

/-- The nested pending word must survive all four anchors and explicit caller
installation. This geometry is required only when insertion reads the word. -/
def pendingProtected (n : Names) (o : Offsets) (c : Context) (base : MachineState)
    (config : RandomProvider.Config) : List Span :=
  Index.storageSpans n o ++ Index.callStack base 135 true ++ Trie.callBuffers c ++
    [(preemptCountAddress.toNat,4)] ++ config.blocks ++ IndexLookup.outputSpan base

/-- Initial resources for retained-heap mixed calls. The supplied input tape
is not reconstructed from the heap. No future call or return is assumed here. -/
def initialCheck (n : Names) (o : Offsets) (c : Context) (base : MachineState)
    (w : World) (ra : UInt64) (config : RandomProvider.Config) : Except String Unit := do
  Sequence.initialCheck n o c base w ra
  Index.callFrameCheck n o c base ra 7
  Insert.providerCheck n o c base ra config
  unless Trie.coverageDataCheck ⟨c.coverage,c.preempt+1024⟩ base.data.dmem do
    throw "insert-sequence.nested-coverage"
  unless (c.preempt+1024) &&& 0x000f0000 == 0 do throw "insert-sequence.nested-hardirq"
  if LookupPendingRead (c.preempt+512) then
    unless base.data.dmem.loadInt softirqPendingAddress 2==some 0 do
      throw "insert-sequence.nested-pending"
    unless spansApart [(softirqPendingAddress.toNat,2)] (pendingProtected n o c base config) do
      throw "insert-sequence.pending-separation"
  unless spansApart config.blocks (IndexLookup.outputSpan base) do
    throw "insert-sequence.private-output-separation"
  unless w.hidden.isSome do throw "insert-sequence.recorded-input-required"

/-- Inspect retained bytes at the original caller locations. This adjusts
only the checker view of the registers; no memory is written or rebuilt. -/
def retainedCheck (n : Names) (o : Offsets) (c : Context) (base current : MachineState)
    (w : World) (ra : UInt64) (config : RandomProvider.Config) : Except String Unit :=
  initialCheck n o c {current with data := {current.data with regs := base.data.regs}} w ra config

end Binary.Pair.InsertSequence
