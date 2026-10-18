import PairInsert
import PairMutatorCapture

namespace Binary.Pair.InsertCapture
open Lean Leanux Leanux.WG

structure RandomService where
  initial : Capture.Endpoint
  returned : Capture.Endpoint
  executedPCs : Array Nat
  deriving FromJson

structure Snapshot extends toMutatorCaptureSnapshot : MutatorCapture.Snapshot where
  randomServices : Array RandomService
  deriving FromJson

/-- Keep the actual recorded service transition separate from Kraken's
instruction trace. Entry bytes/registers are compared before applying it;
only captured changed bytes are installed and their footprint is checked.
Uncaptured private entropy state is outside this test's physical projection. -/
def randomReturn (snapshot : Snapshot) (frame : CallFrame) (index : Nat)
    (r : Run) (value : Nat) : Except String Run := do
  let some service := snapshot.randomServices[index]? | throw "capture.random.missing-boundary"
  let _ ← Capture.compareEndpoint service.initial r.state
  unless service.initial.registers.rip==Insert.randomEntry &&
      service.returned.registers.rip==Insert.entry+0x79 &&
      service.returned.registers.rsp==service.initial.registers.rsp+8 &&
      service.returned.registers.rax==value do throw "capture.random.interface"
  unless service.initial.blocks.size==service.returned.blocks.size do throw "capture.random.block-count"
  let mut memory := r.state.data.dmem
  for (before,after) in service.initial.blocks.zip service.returned.blocks do
    unless before.address==after.address && before.bytes.size==after.bytes.size do
      throw "capture.random.block-layout"
    for j in [:before.bytes.size] do
      let old := before.bytes[j]!
      let byte := after.bytes[j]!
      unless byte<256 do throw "capture.random.byte-width"
      if byte != old then
        let a := after.address+j
        unless within a 1 (frame.stack-2048) 2048 || within a 1 frame.coverage frame.coverageSize do
          throw s!"capture.random.write-footprint: {a}"
        memory := memory.insert (.ofNat 64 a) (.ofNat byte)
  let state ← service.returned.registers.state memory
  for reg in [Reg64.rbx,.rbp,.r12,.r13,.r14,.r15] do
    unless state.data.regs.get64 reg==r.state.data.regs.get64 reg do throw "capture.random.callee-save"
  let used ← readNat state frame.coverage 8
  unless used<snapshot.initial.capacity do throw "capture.random.coverage-count"
  let mut coverage := #[]
  for j in [:used] do
    coverage := coverage.push (← readNat state (frame.coverage+8*(j+1)) 8)
  return {r with state,coverage}

/-- Remove exactly the explicitly sampled service intervals from the native
history. Missing, reordered, overlapping or partial service histories fail. -/
def interpretedPCs (snapshot : Snapshot) : Except String (Array Nat) := do
  let mut remaining := snapshot.executedPCs.toList
  let mut out := #[]
  for service in snapshot.randomServices do
    let (before,after) := remaining.span (· != Insert.randomEntry)
    unless !service.executedPCs.isEmpty && service.executedPCs[0]?==some Insert.randomEntry &&
        after.take service.executedPCs.size==service.executedPCs.toList do
      throw "capture.random.instruction-interval"
    out := out++before.toArray
    remaining := after.drop service.executedPCs.size
  unless !(remaining.contains Insert.randomEntry) do throw "capture.random.unaccounted-entry"
  return out++remaining.toArray

def run (input : ProbeInput) (snapshot : Snapshot) (layout : Json) : Except String Json := do
  unless snapshot.anchor=="insert" && snapshot.executionMode=="sequential" do
    throw "capture.insert.mode"
  unless (← input.trace.getObjValAs? String "id")==snapshot.trace &&
      snapshot.completedOperations.toList==List.range snapshot.operation do throw "capture.insert.provenance"
  let template ← replayRecordedPrefix input.trace input.operation
  let some d := template.k.wg | throw "capture.insert.device"
  let initial ← snapshot.initial.registers.state (← Capture.loadMemory snapshot.initial.blocks)
  let names ← MutatorCapture.names input snapshot.toMutatorCaptureSnapshot layout initial d
  let view ← (reconstruct names input.offsets initial.data.dmem).mapError DecodeError.message
  let world ← MutatorCapture.sourceWorld template view
  let frame ← Capture.callFrame input snapshot.toSnapshot layout initial
  let owner ← (ownerAt names "capture.insert.argument" initial.data.regs.rsi.toNat).mapError DecodeError.message
  let parsed ← Runner.parseTrace input.trace
  let some hidden := parsed.hidden | throw "capture.insert.recorded-input"
  -- This capture selects the second insertion in s2_index_collision. Its
  -- two draws are checked against the independent operation's records.
  let records := (hidden.toList.flatten.filter (·.site==HiddenSite.indexDraw.info.id)).drop 1
  unless records.length==snapshot.randomServices.size do throw "capture.insert.draw-count"
  for (record,service) in records.zip snapshot.randomServices.toList do
    let (value,rest) ← Insert.draw [record]
    unless rest.isEmpty && value==service.returned.registers.rax do throw "capture.insert.draw-value"
  let world := {world with hidden := some records}
  let mut coverage := #[]
  for i in [:snapshot.initial.coverageUsed] do
    coverage := coverage.push (← readNat initial (frame.coverage+8*(i+1)) 8)
  let session : Session := {names,world,binary := {state := initial,coverage}}
  let expected ← interpretedPCs snapshot
  let mut runs := #[]
  for seed in [(0 : UInt64),0xffffffffffffffff] do
    let (after,report) ← Insert.invokeFrom input seed session owner initial frame
      (randomReturn snapshot frame) "actual QEMU service transitions; body not interpreted by Kraken"
    unless after.binary.pcs==expected do throw "capture.insert.instruction-segments"
    let checked ← Capture.compareEndpoint snapshot.returned after.binary.state
    Remove.assertAt names input.offsets (← Capture.loadMemory snapshot.returned.blocks) after.world
    unless after.world.hidden==some [] do throw "capture.insert.remaining-inputs"
    runs := runs.push (Json.mkObj [("seed",toJson seed.toNat),("call",report),("compared_bytes",toJson checked)])
  return Json.mkObj [("status",toJson "pass"),
    ("execution_scope",toJson "actual anchor/KCOV/BH instructions under Kraken, sampled native random-service transitions"),
    ("input_origin",toJson "actual entry projection, allocation identities from recorded prefix, draws checked against independent recording"),
    ("native_instructions",toJson snapshot.executedPCs.size),("interpreted_instructions",toJson expected.size),
    ("random_services",toJson snapshot.randomServices.size),("capacity",toJson snapshot.initial.capacity),
    ("runs",toJson runs)]

end Binary.Pair.InsertCapture
