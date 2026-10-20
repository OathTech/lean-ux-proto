import PairLoopCheck
import CommonBitsCallerState

namespace Binary.Pair.Common
open CommonBits

def callInput (s : MachineData) (bits stored query : Nat) (returnPC : Int64) : Input := {
  node := s.regs.rdi, key := s.regs.rsi, stack := s.regs.rsp-40
  family := .ofNat 8 bits
  stored32 := .ofNat stored, query32 := .ofNat query
  storedHigh := .ofNat (stored/2^64), queryHigh := .ofNat (query/2^64)
  storedLow := .ofNat (stored%2^64), queryLow := .ofNat (query%2^64)
  savedBx := s.regs.rbx, savedBp := s.regs.rbp, savedR12 := s.regs.r12, savedR13 := s.regs.r13
  returnAddress := returnPC.toUInt64 }

/-- Read only the metadata consulted at the current preemption level. -/
def readContext (m : DataMem) : Except String CommonBitsCoverage.Context := do
  let read (address size : Nat) := (word m "common.context" address size).mapError DecodeError.message
  let task ← read TrustBase.currentTaskAddress.toNat 8
  let preempt := BitVec.ofNat 32 (← read TrustBase.preemptCountAddress.toNat 4)
  let soft ← if TrustBase.LookupSoftRead preempt then read (task+0x704) 4 else pure 0
  let base : TrustBase.KcovLayout := ⟨.ofNat 64 task,0,0,0,.ofNat 32 soft⟩
  let mode ← if TrustBase.LookupModeRead base preempt then read (task+0x6e0) 4 else pure 0
  let coverage := {base with mode := .ofNat 32 mode}
  let needed := (CommonBitsCoverage.Context.mk coverage preempt).Needed
  let capacity ← if needed then read (task+0x6e4) 4 else pure 0
  let area ← if needed then read (task+0x6e8) 8 else pure 0
  return ⟨{coverage with capacity := .ofNat 32 capacity,area := .ofNat 64 area},preempt⟩

/-- A runtime version of the existing physical caller premises. It checks
input words and separation, not execution or a predicted helper result. -/
def callerCheck (i : Input) (c : CommonBitsCoverage.Context) (s : MachineData)
    (returnPC : Int64) : Bool :=
  Trie.frameCheck c s &&
  (i.node==s.regs.rdi && i.key==s.regs.rsi && i.stack==s.regs.rsp-40 &&
    i.family==s.regs.get (.low .rdx .W8) && i.savedBx==s.regs.rbx &&
    i.savedBp==s.regs.rbp && i.savedR12==s.regs.r12 && i.savedR13==s.regs.r13 &&
    i.returnAddress==returnPC.toUInt64) &&
  i.keyWords.all (fun word => s.dmem.loadInt word.address word.width == some word.value) &&
  spansApart (i.keyWords.map fun word => (word.address.toNat,word.width))
    ([((s.regs.rsp.toBitVec-48).toNat,48)] ++ Trie.writeSpans c)

end Binary.Pair.Common
