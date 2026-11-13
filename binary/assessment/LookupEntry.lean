import PairCapture
import PairLookupCheck

/-! Evaluate the existing theorem's executable entry predicate on unchanged
captured memory. This is an assessment command, not a replacement predicate.
`PairLookupPre.pre_lookup` proves that a successful callBoundary supplies the
original Pre_lookup. This command does not check universal permissions or
establish an interrupt model. -/
open Lean Leanux Binary Binary.Pair

def assess (input : ProbeInput) (snapshot : Capture.Snapshot) (layout : Json) : Except String Json := do
  unless snapshot.executionMode == "sequential" do throw "expected sequential capture"
  unless (← input.trace.getObjValAs? String "id") == snapshot.trace &&
      input.operation == snapshot.operation &&
      snapshot.completedOperations.toList == List.range snapshot.operation do
    throw "capture invocation mismatch"
  let w ← replayPrefix input.trace input.operation
  let some d := w.wg.dev | throw "missing source device"
  let s ← snapshot.initial.registers.state (← Capture.loadMemory snapshot.initial.blocks)
  let n ← Capture.names input snapshot layout s d
  let f ← Capture.callFrame input snapshot layout s
  let context ← Index.readContext s.data.dmem
  IndexLookup.callBoundary n input.offsets context s w input.query [.handshake] (.ofNat f.returnPC)
  let (answer, _) ← (Source.indexLookup [.handshake] input.query).run w |>.mapError Stop.message
  let bad := {s with pc := s.pc + 1}
  match IndexLookup.callBoundary n input.offsets context bad w input.query [.handshake] (.ofNat f.returnPC) with
  | .ok () => throw "negative control admitted wrong entry PC"
  | .error error =>
    unless error == "lookup.call.arguments" do throw s!"negative control failed elsewhere: {error}"
  return Json.mkObj [("status", toJson "pass"), ("predicate", toJson "IndexLookup.callBoundary"),
    ("trace", toJson snapshot.trace), ("source_answer", toJson (reprStr answer)),
    ("capacity", toJson snapshot.initial.capacity),
    ("captured_words", toJson snapshot.initial.coverageCapturedWords),
    ("entry_preempt", toJson f.entryPreempt), ("wrong_pc_rejected", toJson true)]

def main (args : List String) : IO UInt32 := do
  let [inputPath, snapshotPath, layoutPath] := args
    | IO.eprintln "usage: LookupEntry INPUT.json SNAPSHOT.json LAYOUTS.json"; return 1
  let input := Json.parse (← IO.FS.readFile inputPath) >>= fromJson? (α := ProbeInput)
  let snapshot := Json.parse (← IO.FS.readFile snapshotPath) >>= fromJson? (α := Capture.Snapshot)
  let layout := Json.parse (← IO.FS.readFile layoutPath)
  match (do assess (← input) (← snapshot) (← layout)) with
  | .ok report => IO.println report.compress; return 0
  | .error error => IO.eprintln s!"FAIL: {error}"; return 1
