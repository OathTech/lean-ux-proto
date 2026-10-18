import PairInsertCapture
open Lean Binary.Pair.InsertCapture

def main (args : List String) : IO UInt32 := do
  let [inputPath,snapshotPath,layoutPath] := args
    | IO.eprintln "usage: binary-pair-insert-capture INPUT.json SNAPSHOT.json LAYOUTS.json"; return 1
  let input := Json.parse (← IO.FS.readFile inputPath) >>= fromJson? (α := ProbeInput)
  let snapshot := Json.parse (← IO.FS.readFile snapshotPath) >>= fromJson? (α := Snapshot)
  let layout := Json.parse (← IO.FS.readFile layoutPath)
  match (do run (← input) (← snapshot) (← layout)) with
  | .ok result => IO.println result.compress; return 0
  | .error e => IO.eprintln s!"FAIL: {e}"; return 1
