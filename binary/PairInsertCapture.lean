import SourceAdapter
import PairInsert
import PairMutatorCapture
import PairRandomRun
import PairInsertProvider

namespace Binary.Pair.InsertCapture
open Lean Leanux Leanux.WG

structure RandomService where
  initial : Capture.Endpoint
  returned : Capture.Endpoint
  executedPCs : Array Nat
  deriving FromJson

structure KernelIdentity where
  checked : Bool
  expected : String
  actual : String
  deriving FromJson

structure Snapshot extends toMutatorCaptureSnapshot : MutatorCapture.Snapshot where
  kernel : KernelIdentity
  image_sha256 : String
  kraken : String
  randomServices : Array RandomService
  deriving FromJson

structure PrivateState where
  blocks : List (Nat × Nat)
  remoteNodes : List Nat
  deriving FromJson

def PrivateState.config (s : PrivateState) : RandomProvider.Config := ⟨s.blocks,s.remoteNodes⟩

/-- Capture identity is required and checked before replay. These constants
identify the image and semantics compiled into this executable. The host
driver additionally verifies the current dependency tree and oracle file. -/
def checkIdentity (kernel : KernelIdentity) (image kraken : String) : Except String Unit := do
  unless kernel.checked && kernel.expected==TrustBase.kernelIdentity &&
      kernel.actual==TrustBase.kernelIdentity do throw "capture.insert.kernel-identity"
  unless image==TrustBase.elfSha256 do throw "capture.insert.image-sha256"
  unless kraken==TrustBase.krakenCommit do throw "capture.insert.kraken-pin"

/-- Run the decoded service body from the actual captured entry heap. The
native endpoints and instruction sequence are comparisons, never transitions. -/
def randomReturn (snapshot : Snapshot) (privateState : PrivateState) (seed : UInt64)
    (frame : CallFrame) (index : Nat) (r : Run) (value : Nat) : Except String Run := do
  let some service := snapshot.randomServices[index]? | throw "capture.random.missing-boundary"
  let _ ← Capture.compareEndpoint service.initial r.state
  unless service.initial.registers.rip==Insert.randomEntry &&
      service.returned.registers.rip==Insert.entry+0x79 &&
      service.returned.registers.rsp==service.initial.registers.rsp+8 do throw "capture.random.interface"
  let context ← Index.readContext r.state.data.dmem
  RandomProvider.readyCheck privateState.config context r.state
  let after ← RandomRun.execute seed snapshot.instructionBudget r.state (.ofNat (Insert.entry+0x79))
    (some service.executedPCs)
  RandomRun.physicalPost privateState.config context r.state after (.ofNat (Insert.entry+0x79))
  unless after.state.data.regs.rax.toNat==value do throw "capture.random.recorded-draw"
  unless after.pcs==RandomRun.instructionPCs service.executedPCs do throw "capture.random.instructions"
  let _ ← Capture.compareEndpoint service.returned after.state
  let used ← readNat after.state frame.coverage 8
  unless used<snapshot.initial.capacity do throw "capture.random.coverage-count"
  let mut coverage := #[]
  for j in [:used] do
    coverage := coverage.push (← readNat after.state (frame.coverage+8*(j+1)) 8)
  return {r with
    state := after.state,coverage,pcs := r.pcs++after.pcs,
    reads := r.reads++after.reads,writes := r.writes++after.writes,
    undefinedCount := r.undefinedCount+after.undefinedCount}

def run (input : ProbeInput) (snapshot : Snapshot) (privateState : PrivateState) (layout : Json) : Except String Json := do
  checkIdentity snapshot.kernel snapshot.image_sha256 snapshot.kraken
  unless snapshot.anchor=="insert" && snapshot.executionMode=="sequential" do
    throw "capture.insert.mode"
  unless (← input.trace.getObjValAs? String "id")==snapshot.trace &&
      snapshot.completedOperations.toList==List.range snapshot.operation do throw "capture.insert.provenance"
  let template ← replayRecordedPrefix input.trace input.operation
  let some d := template.wg.dev | throw "capture.insert.device"
  let initial ← snapshot.initial.registers.state (← Capture.loadMemory snapshot.initial.blocks)
  -- A cheap independent endpoint control for the newly represented IF bit.
  -- Its empty byte list isolates flag comparison; the real run compares all bytes.
  let flagsControl : Capture.Endpoint := {registers := {snapshot.initial.registers with
    eflags := snapshot.initial.registers.eflags ^^^ 512},blocks := #[]}
  let flagsRejected ← match Capture.compareEndpoint flagsControl initial with
    | .ok _ => throw "capture.insert.control: changed IF accepted"
    | .error e => do
      unless e.startsWith "captured endpoint system flags" do
        throw s!"capture.insert.control: changed IF failed elsewhere: {e}"
      pure e
  let names ← MutatorCapture.names input snapshot.toMutatorCaptureSnapshot layout initial d
  let view ← (reconstruct names input.offsets initial.data.dmem).mapError DecodeError.message
  let world ← MutatorCapture.sourceWorld template view
  let frame ← Capture.callFrame input snapshot.toSnapshot layout initial
  Insert.providerCheck names input.offsets (← Index.readContext initial.data.dmem)
    initial (.ofNat frame.returnPC) privateState.config
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
  let world := {world with ambient := {world.ambient with hidden := some records}}
  let mut coverage := #[]
  for i in [:snapshot.initial.coverageUsed] do
    coverage := coverage.push (← readNat initial (frame.coverage+8*(i+1)) 8)
  let session : Session := {names,world,binary := {state := initial,coverage}}
  unless spansApart privateState.blocks
      (Index.storageSpans names input.offsets ++ Index.callStack initial 7 true) do
    throw "capture.random.private-protected-alias"
  let expected := RandomRun.instructionPCs snapshot.executedPCs
  let mut runs := #[]
  for seed in [(0 : UInt64),0xffffffffffffffff] do
    let (after,report) ← Insert.invokeFrom input seed session owner initial frame
      (randomReturn snapshot privateState seed frame) "actual decoded random body from captured private memory"
      privateState.blocks
    unless after.binary.pcs==expected do throw "capture.insert.instruction-segments"
    let checked ← Capture.compareEndpoint snapshot.returned after.binary.state
    Remove.assertAt names input.offsets (← Capture.loadMemory snapshot.returned.blocks) after.world
    unless after.world.hidden==some [] do throw "capture.insert.remaining-inputs"
    runs := runs.push (Json.mkObj [("seed",toJson seed.toNat),("call",report),("compared_bytes",toJson checked)])
  return Json.mkObj [("status",toJson "pass"),
    ("execution_scope",toJson "actual anchor, KCOV, BH and random-service instructions under Kraken from captured memory"),
    ("input_origin",toJson "actual entry projection, allocation identities from recorded prefix, draws checked against independent recording"),
    ("native_single_step_stops",toJson snapshot.executedPCs.size),("interpreted_instructions",toJson expected.size),
    ("REP_validation",toJson "each native repeat-stop multiplicity checked against actual entry RCX"),
    ("random_services",toJson snapshot.randomServices.size),("capacity",toJson snapshot.initial.capacity),
    ("system_flags_control",toJson flagsRejected),
    ("runs",toJson runs)]

end Binary.Pair.InsertCapture
