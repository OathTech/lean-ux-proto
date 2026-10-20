import PairInsertCapture
open Lean Binary.Pair.InsertCapture

def main (args : List String) : IO UInt32 := do
  let [inputPath,snapshotPath,layoutPath] := args
    | IO.eprintln "usage: binary-pair-insert-capture INPUT.json SNAPSHOT.json LAYOUTS.json"; return 1
  let input := Json.parse (← IO.FS.readFile inputPath) >>= fromJson? (α := ProbeInput)
  let raw := Json.parse (← IO.FS.readFile snapshotPath)
  let snapshot := raw >>= fromJson? (α := Snapshot)
  let privateState := do
    let initial ← (← raw).getObjVal? "initial"
    fromJson? (α := PrivateState) (← initial.getObjVal? "randomPrivate")
  let layout := Json.parse (← IO.FS.readFile layoutPath)
  match (do run (← input) (← snapshot) (← privateState) (← layout)) with
  | .ok result => IO.println result.compress; return 0
  | .error e => IO.eprintln s!"FAIL: {e}"; return 1
