import ReplacementObserve
import PairMutatorCapture

open Lean Leanux Binary.Pair

/-- This executable checks the Device projection consumed by the existing
replacement predicate. Other World fields are unused by that predicate;
the containing caller is executed independently by ReplacementObserve.
The Python driver must first establish same-boot record/dispatch alignment. -/
def admission (input : ProbeInput) (snapshot : MutatorCapture.Snapshot) (layout : Json)
    (operation ordinal : Nat) : Except String Json := do
  unless snapshot.anchor == "replace" && snapshot.executionMode == "sequential" &&
      snapshot.operation == operation && snapshot.completedOperations.toList == List.range operation &&
      (← input.trace.getObjValAs? String "id") == snapshot.trace do
    throw "observed-entry.workload-or-mode"
  let selected ← Binary.ReplacementObserve.select input operation ordinal
  let entry := selected.entry
  let some d := entry.device | throw "observed-entry.no-device"
  let initial ← snapshot.initial.registers.state (← Capture.loadMemory snapshot.initial.blocks)
  let n ← MutatorCapture.names input snapshot layout initial d
  let peerIdOffset ← Capture.member layout "wg_peer" "internal_id"
  for (id, address) in n.peers do
    let some peer := d.peers[id]? | throw "observed-entry.peer-absent"
    unless (← readNat initial (address + peerIdOffset) 8) == peer.internalId do
      throw "observed-entry.peer-lifetime"
  let op ← MutatorCapture.call snapshot n initial
  let .replace pid kid := op | throw "observed-entry.not-replacement"
  unless pid == entry.peer && kid == entry.keypair do throw "observed-entry.arguments"
  let template := selected.replay.world
  let world := {template with wg := {template.wg with
    dev := entry.device, peerCounter := entry.peerCounter, keypairCounter := entry.keypairCounter}}
  let controls ← MutatorCapture.entryControls input snapshot layout initial n d world
  let frame ← Capture.callFrame input snapshot.toSnapshot layout initial
  let context ← Index.readContext initial.data.dmem
  let erased := {world with wg := {world.wg with dev := some {d with indexTable := []}}}
  let sourceControl ← MutatorCapture.rejected "erased independently observed source table"
    (Replace.callBoundary n input.offsets context initial erased entry.peer entry.keypair (.ofNat frame.returnPC))
  let replay ← MutatorCapture.replayAt input snapshot layout initial n world
  return Json.mkObj [("status", toJson "predicate-and-replay-pass"),
    ("scope", toJson "existing Replace.callBoundary on the independently observed Device; complete sequential instruction and return replay; provenance must also pass the Python driver"),
    ("source", Binary.ReplacementObserve.report selected operation ordinal),
    ("entry_controls", toJson (controls.push sourceControl)), ("replay", replay)]

def main (args : List String) : IO UInt32 := do
  let [inputPath, snapshotPath, layoutPath, operationText, ordinalText] := args
    | IO.eprintln "usage: binary-replacement-admit INPUT.json SNAPSHOT.json LAYOUTS.json OPERATION ORDINAL"; return 1
  let some operation := operationText.toNat? | IO.eprintln "invalid operation"; return 1
  let some ordinal := ordinalText.toNat? | IO.eprintln "invalid ordinal"; return 1
  let input := Json.parse (← IO.FS.readFile inputPath) >>= fromJson? (α := ProbeInput)
  let snapshot := Json.parse (← IO.FS.readFile snapshotPath) >>= fromJson? (α := MutatorCapture.Snapshot)
  let layout := Json.parse (← IO.FS.readFile layoutPath)
  match (do admission (← input) (← snapshot) (← layout) operation ordinal) with
  | .ok result => IO.println result.compress; return 0
  | .error error => IO.eprintln s!"FAIL: {error}"; return 1
