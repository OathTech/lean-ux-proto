import PairIndexStorage
import PairCallCheck

namespace Binary.Pair.Index
open TrustBase CommonBitsCoverage

def callStack (s : MachineState) (words : Nat) (returnWord : Bool) : List Span :=
  [((s.data.regs.rsp.toBitVec-.ofNat 64 (8*words)).toNat,8*words+(if returnWord then 8 else 0))]

/-- Reconstruct the callback context from the current memory. Fields omitted
by both phases are unused context parameters, not defaulted memory reads. -/
def readContext (m : DataMem) : Except String Context := do
  let read (address size : Nat) := (word m "index.call.context" address size).mapError DecodeError.message
  let task ← read currentTaskAddress.toNat 8
  let old ← read preemptCountAddress.toNat 4
  let preempt := BitVec.ofNat 32 old
  let soft ← if LookupSoftRead preempt ∨ LookupSoftRead (preempt+512)
    then read (task+0x704) 4 else pure 0
  let base : KcovLayout := ⟨.ofNat 64 task,0,0,0,.ofNat 32 soft⟩
  let mode ← if LookupModeRead base preempt ∨ LookupModeRead base (preempt+512)
    then read (task+0x6e0) 4 else pure 0
  let coverage := {base with mode := .ofNat 32 mode}
  let needed := (Context.mk coverage preempt).Needed ∨ (Context.mk coverage (preempt+512)).Needed
  let capacity ← if needed then read (task+0x6e4) 4 else pure 0
  let area ← if needed then read (task+0x6e8) 8 else pure 0
  return ⟨{coverage with capacity := .ofNat 32 capacity,area := .ofNat 64 area},preempt⟩

/-- Shared physical readiness for an index mutator. It checks the present
memory and allocation geometry; it says nothing about future execution. -/
def callFrameCheck (n : Names) (o : Offsets) (c : Context)
    (s : MachineState) (ra : UInt64) (words : Nat) : Except String Unit := do
  unless s.data.regs.rsp.toNat % 8 == 0 &&
      s.data.dmem.loadInt s.data.regs.rsp.toBitVec 8 == some (ra.toNat : Int) do
    throw "index.call.abi-return"
  unless (List.range words).all (fun i =>
      (s.data.dmem.loadInt (s.data.regs.rsp.toBitVec-.ofNat 64 ((i+1)*8)) 8).isSome) do
    throw "index.call.stack-mapping"
  unless Trie.coverageCheck c s.data.dmem &&
      Trie.coverageDataCheck ⟨c.coverage,c.preempt+512⟩ s.data.dmem do
    throw "index.call.coverage-phases"
  unless (c.preempt+512) &&& 0x000f0000 == 0 do throw "index.call.hardirq"
  unless (if LookupPendingRead c.preempt then s.data.dmem.loadInt softirqPendingAddress 2 == some 0 else true) do
    throw "index.call.pending-softirq"
  let preempt := [(preemptCountAddress.toNat,4)]
  unless spansApart (storageSpans n o) (callStack s words true ++ Trie.callServices c) do
    throw "index.call.heap-separation"
  unless spansApart (Trie.callServices c) (callStack s words false) do
    throw "index.call.service-stack"
  unless spansApart (Trie.callBuffers c) (callStack s words true ++ Trie.callMetadata c ++ preempt) do
    throw "index.call.buffer-separation"
  unless spansApart (callStack s words true ++ Trie.callMetadata c ++ Trie.callHeaders c) preempt do
    throw "index.call.preempt-separation"

end Binary.Pair.Index
