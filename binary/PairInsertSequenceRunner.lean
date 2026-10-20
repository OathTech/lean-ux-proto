import SourceAdapter
import PairInsertSequenceCheck
import PairSequenceRunner
import PairRandomRun

namespace Binary.Pair.InsertSequence
open Lean Leanux Leanux.WG TrustBase

/-- Build the labelled initial private fixture once. Later calls retain it.
The steering tape is installed in the actual instrumented provider layout. -/
def withProvider (m : DataMem) (task : Nat) (records : List HiddenRecord) :
    Except String (DataMem×RandomProvider.Config) := do
  unless records.length≤64 do throw "insert-sequence.fixture.steering-capacity"
  let cached := RandomRun.cachedState true
  let mut memory := m
  for (a,size) in RandomRun.privateConfig.blocks do
    for i in [:size] do
      let some byte := cached.data.dmem.get? (.ofNat 64 (a+i)) |
        throw "insert-sequence.fixture.private-byte"
      memory := memory.insert (.ofNat 64 (a+i)) byte
  let extra := [(task+RandomProvider.Layout.taskObject,16),(task+RandomProvider.Layout.taskDropped,4),(0xa00000,56),
    (0xb00000,16+88*records.length),(RandomProvider.Layout.sequenceAddress,8)]
  for (a,size) in extra do
    for i in [:size] do memory := put memory (a+i) 1 0
  memory := put memory (task+RandomProvider.Layout.taskObject) 8 0xa00000
  memory := put memory (0xa00000+RandomProvider.Layout.objectSteer) 8 0xb00000
  memory := put memory (0xb00000+RandomProvider.Layout.steerCount) 4 records.length
  for (record,i) in records.zipIdx do
    let (value,rest) ← Insert.draw [record]
    unless rest.isEmpty do throw "insert-sequence.fixture.record"
    let a := 0xb00000+RandomProvider.Layout.steerEntries+i*RandomProvider.Layout.entrySize
    memory := put memory a 8 (Insert.entry+0x79)
    -- The C steering kind is RANDOM (104), not the mirror site identifier.
    memory := put memory (a+32) 4 104
    memory := put memory (a+RandomProvider.Layout.entryLength) 4 4
    memory := put memory (a+48) 4 value
  return (memory,{blocks := RandomRun.privateConfig.blocks++extra})

def randomReturn (config : RandomProvider.Config) (seed : UInt64)
    (ordinal : Nat) (r : Run) (value : Nat) : Except String Run := do
  let c ← Index.readContext r.state.data.dmem
  RandomProvider.readyCheck config c r.state
  let after ← RandomRun.execute seed 20000 r.state (.ofNat (Insert.entry+0x79))
  RandomRun.physicalPost config c r.state after (.ofNat (Insert.entry+0x79))
  unless after.state.data.regs.rax.toNat==value do
    throw s!"insert-sequence.random.draw: ordinal={ordinal}, expected={value}, actual={after.state.data.regs.rax.toNat}, head={← readNat after.state 0xb00004 4}, mismatches={← readNat after.state 0xb00008 4}"
  let used ← readNat after.state c.coverage.area.toNat 8
  unless used≤c.coverage.capacity.toNat do throw "insert-sequence.random.coverage-count"
  let mut coverage := #[]
  for i in [:used] do coverage := coverage.push (← readNat after.state (c.coverage.area.toNat+8*(i+1)) 8)
  return {r with
    state := after.state,coverage,pcs := r.pcs++after.pcs,
    reads := r.reads++after.reads,writes := r.writes++after.writes,
    undefinedCount := r.undefinedCount+after.undefinedCount}

def runCalls (input : ProbeInput) (seed : UInt64) (w : World) (calls : List Call)
    (capacity : Nat) (preempt : Nat := 0) : Except String Json := do
  let fixture ← Replace.fixture input w
  let original ← Index.readContext fixture.binary.state.data.dmem
  let some records := w.hidden | throw "insert-sequence.fixture.inputs"
  let memory := put fixture.binary.state.data.dmem (original.coverage.task.toNat+0x6e4) 4 capacity
  let memory := put memory TrustBase.preemptCountAddress.toNat 4 preempt
  let (memory,config) ← withProvider memory original.coverage.task.toNat records
  let base : MachineState := ⟨{dmem := memory,system := {cpl := 0,bits := 512},regs := {
    rsp := .ofNat stackAddr,rcx := .ofNat outputAddr,rbx := 17,rbp := 34,
    r12 := 51,r13 := 68,r14 := 85,r15 := 102}},.ofNat stopAddr⟩
  let c ← Index.readContext memory
  initialCheck fixture.names input.offsets c base w (.ofNat stopAddr) config
  let reject (label expected : String) (result : Except String Unit) : Except String Unit :=
    match result with
    | .ok _ => .error s!"insert-sequence.control.{label}: invalid state accepted"
    | .error error => if error==expected then .ok () else
        .error s!"insert-sequence.control.{label}: failed elsewhere: {error}"
  reject "input-tape" "insert-sequence.recorded-input-required"
    (initialCheck fixture.names input.offsets c base {w with ambient := {w.ambient with hidden := none}} (.ofNat stopAddr) config)
  reject "private-output-alias" "insert-sequence.private-output-separation"
    (initialCheck fixture.names input.offsets c base w (.ofNat stopAddr)
      {config with blocks := config.blocks++IndexLookup.outputSpan base})
  if TrustBase.LookupPendingRead (c.preempt+512) then
    let bad := {base with data := {base.data with
      dmem := put memory TrustBase.softirqPendingAddress.toNat 2 1}}
    reject "nested-pending" "insert-sequence.nested-pending"
      (initialCheck fixture.names input.offsets c bad w (.ofNat stopAddr) config)
  let mut session := {fixture with binary := {fixture.binary with state := base}}
  let mut reports := #[]
  for call in calls do
    let initial ← prepare session.names base (.ofNat stopAddr) call session.binary.state
    let (answer,world) ← (source call).run session.world |>.mapError Stop.message
    let after ← match call with
      | .insert owner => do
        Insert.providerCheck session.names input.offsets c initial (.ofNat stopAddr) config
        let (after,_) ← Insert.invokeFrom input seed session owner initial
          {coverageSize := capacity*8} (randomReturn config seed)
          "actual decoded random body; retained private state and input tape" config.blocks
        pure after
      | .existing old => do
        match old with
        | .lookup query kinds => IndexLookup.callBoundary session.names input.offsets c initial session.world query kinds (.ofNat stopAddr)
        | .remove owner => Remove.callBoundary session.names input.offsets c initial session.world owner (.ofNat stopAddr)
        | .replace pid kid => Replace.callBoundary session.names input.offsets c initial session.world pid kid (.ofNat stopAddr)
        let prior := {session.binary with state := initial,history := #[initial],pcs := #[],reads := #[],writes := #[]}
        let run ← runUntil input.instructions input.labels input.hooks input.preempt initial seed true
          100000 c.preempt.toNat #[] (some prior) stopAddr (some #[])
          (some fun state => match KcovPlan .pc state with
            | none => .error "insert-sequence.coverage-inputs"
            | some writes => .ok (!writes.isEmpty))
        pure {session with world,binary := run,call := session.call+1}
    let run := after.binary
    Remove.assertAt after.names input.offsets run.state.data.dmem world
    unless after.world.hidden==world.hidden do throw "insert-sequence.input-cursor"
    retainedCheck after.names input.offsets c base run.state world (.ofNat stopAddr) config
    match answer with
    | .existing answer => Sequence.resultCheck after.names initial run.state answer
    | .insert value => unless run.state.data.regs.rax.toNat==value do throw "insert-sequence.insert.result"
    unless run.state.pc.toBitVec.toNat==stopAddr && run.state.data.regs.rsp.toNat==stackAddr+8 do
      throw "insert-sequence.return.abi"
    for reg in [Reg64.rbx,.rbp,.r12,.r13,.r14,.r15] do
      unless run.state.data.regs.get64 reg==initial.data.regs.get64 reg do throw "insert-sequence.return.callee-save"
    unless (← readNat run.state coverageAddr 8)==run.coverage.size do throw "insert-sequence.coverage-count"
    for i in [:run.coverage.size] do
      unless (← readNat run.state (coverageAddr+8*(i+1)) 8)==run.coverage[i]! do throw "insert-sequence.coverage-record"
    for (a,size) in run.writes do
      unless within a size (stackAddr-1080) 1088 || within a size outputAddr 8 ||
          within a size coverageAddr (8*capacity) || within a size input.preempt 4 ||
          within a size after.names.table input.offsets.tableSize ||
          after.names.owners.any (fun (_,base) => within a size base input.offsets.entrySize) ||
          after.names.peers.any (fun (_,base) => within a size (base+input.offsets.peerRefcount) 4) ||
          config.blocks.any (fun (base,width) => within a size base width) do
        throw s!"insert-sequence.write-footprint:{a}/{size}"
    reports := reports.push (Json.mkObj [("call",toJson (reprStr call)),("answer",toJson (reprStr answer)),
      ("instructions",toJson run.pcs.size),("coverage_used",toJson run.coverage.size),
      ("remaining_inputs",toJson (world.hidden.map List.length))])
    session := {after with world}
  unless session.world.hidden==some [] do throw "insert-sequence.unconsumed-input"
  unless (← readNat session.binary.state (0xb00000+RandomProvider.Layout.steerHead) 4)==records.length do
    throw "insert-sequence.unconsumed-steering"
  return Json.mkObj [("seed",toJson seed.toNat),("capacity",toJson capacity),("calls",toJson reports)]

end Binary.Pair.InsertSequence
