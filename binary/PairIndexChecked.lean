import PairLookupCheck

namespace Binary.Pair.IndexLookup
open Lean Leanux Leanux.WG

/-- Runs the assertion used by the theorem around the existing paired
segment runner. The same allocation interpretation and heap survive return. -/
def runFrom (input : ProbeInput) (seed : UInt64) (session : Session) (query : Nat)
    (kinds : List IndexKind) (initial : MachineState) (frame : CallFrame) : Except String (Session×Json) := do
  let coverage ← Index.readContext initial.data.dmem
  callBoundary session.names input.offsets coverage initial session.world query kinds (.ofNat frame.returnPC)
  let (next,report) ← Pair.lookupFrom input seed session query kinds initial frame
  Remove.assertAt next.names input.offsets next.binary.state.data.dmem next.world
  unless Trie.coverageCheck coverage next.binary.state.data.dmem &&
      Trie.coverageDataCheck ⟨coverage.coverage,coverage.preempt+512⟩ next.binary.state.data.dmem do
    throw "lookup.return.coverage-phases"
  return (next,report)

def invoke (input : ProbeInput) (seed : UInt64) (session : Session) (query : Nat)
    (kinds : List IndexKind) : Except String (Session×Json) := do
  let regs : Reg64s := {
    rdi := .ofNat session.names.table, rsi := .ofNat (Pair.kindMask kinds)
    rdx := .ofNat query, rcx := .ofNat outputAddr, rsp := .ofNat stackAddr
    rbx := 0x11, rbp := 0x22, r12 := 0x33, r13 := 0x44, r14 := 0x55, r15 := 0x66}
  runFrom input seed session query kinds ⟨{session.binary.state.data with regs},Image.Lookup.entry⟩ {}

end Binary.Pair.IndexLookup
