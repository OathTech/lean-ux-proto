import PairSequenceCheck

namespace Binary.Pair.Sequence
open Lean Leanux Leanux.WG

def resultCheck (n : Names) (entry final : MachineState) (answer : Answer) : Except String Unit := do
  match answer with
  | .remove => pure ()
  | .replace value =>
    unless final.data.regs.rax.toNat%256==(if value then 1 else 0) do throw "sequence.replace.result"
  | .lookup none =>
    unless final.data.regs.rax==0 do throw "sequence.lookup.null-result"
  | .lookup (some (owner,pid)) =>
    let ownerAddress ← addressOf n owner
    let some (_,peerAddress) := n.peers.find? (·.1==pid) | throw "sequence.lookup.unknown-peer"
    unless final.data.regs.rax.toNat==ownerAddress &&
        (← readNat final entry.data.regs.rcx.toNat 8)==peerAddress do throw "sequence.lookup.hit-result"

/-- One retained heap and Names; prepare uses exactly the caller transition
in the finite-sequence theorem. Bounds limit the test, not proof termination. -/
def runCalls (input : ProbeInput) (seed : UInt64) (w : World) (calls : List Call)
    (capacity : Nat := coverageBytes/8) : Except String Json := do
  let fixture ← Replace.fixture input w
  let original ← Index.readContext fixture.binary.state.data.dmem
  let memory := put fixture.binary.state.data.dmem (original.coverage.task.toNat+0x6e4) 4 capacity
  let base : MachineState := ⟨{dmem := memory,regs := {
    rsp := .ofNat stackAddr,rcx := .ofNat outputAddr,rbx := 17,rbp := 34,
    r12 := 51,r13 := 0xabc044,r14 := 85,r15 := 102}},.ofNat stopAddr⟩
  let c ← Index.readContext memory
  initialCheck fixture.names input.offsets c base w (.ofNat stopAddr)
  let mut session := {fixture with binary := {fixture.binary with state := base}}
  let mut reports := #[]
  for call in calls do
    let initial ← prepare session.names base (.ofNat stopAddr) call session.binary.state
    match call with
    | .lookup query kinds => IndexLookup.callBoundary session.names input.offsets c initial session.world query kinds (.ofNat stopAddr)
    | .remove owner => Remove.callBoundary session.names input.offsets c initial session.world owner (.ofNat stopAddr)
    | .replace pid kid => Replace.callBoundary session.names input.offsets c initial session.world pid kid (.ofNat stopAddr)
    let (answer,world) ← (source call).run session.world |>.mapError Stop.message
    let prior := {session.binary with state := initial,history := #[initial],pcs := #[],reads := #[],writes := #[]}
    let run ← runUntil input.instructions input.labels input.hooks input.preempt initial seed true
      100000 0 #[] (some prior) stopAddr (some #[])
      (some fun state => match TrustBase.KcovPlan .pc state with
        | none => .error "sequence.coverage-inputs"
        | some writes => .ok (!writes.isEmpty))
    Remove.assertAt session.names input.offsets run.state.data.dmem world
    residentCheck session.names input.offsets run.state.data.dmem
    resultCheck session.names initial run.state answer
    unless run.state.pc.toBitVec.toNat==stopAddr && run.state.data.regs.rsp.toNat==stackAddr+8 do
      throw "sequence.return.abi"
    for reg in [Reg64.rbx,.rbp,.r12,.r13,.r14,.r15] do
      unless run.state.data.regs.get64 reg==initial.data.regs.get64 reg do throw "sequence.return.callee-save"
    unless Trie.coverageCheck c run.state.data.dmem &&
        Trie.coverageDataCheck ⟨c.coverage,c.preempt+512⟩ run.state.data.dmem do throw "sequence.return.services"
    unless (← readNat run.state coverageAddr 8)==run.coverage.size do throw "sequence.return.coverage-count"
    for i in [:run.coverage.size] do
      unless (← readNat run.state (coverageAddr+8*(i+1)) 8)==run.coverage[i]! do throw "sequence.return.coverage-record"
    for (a,size) in run.writes do
      unless within a size (stackAddr-104) 112 || within a size outputAddr 8 ||
          within a size coverageAddr (8*capacity) || within a size input.preempt 4 ||
          within a size session.names.table input.offsets.tableSize ||
          session.names.owners.any (fun (_,base) => within a size base input.offsets.entrySize) ||
          session.names.peers.any (fun (_,base) => within a size (base+input.offsets.peerRefcount) 4) do
        throw s!"sequence.write-footprint:{a}/{size}"
    reports := reports.push (Json.mkObj [("call",toJson (reprStr call)),("answer",toJson (reprStr answer)),
      ("instructions",toJson run.pcs.size),("coverage_used",toJson run.coverage.size)])
    session := {session with world,binary := run,call := session.call+1}
  return Json.mkObj [("seed",toJson seed.toNat),("capacity",toJson capacity),("calls",toJson reports)]

end Binary.Pair.Sequence
