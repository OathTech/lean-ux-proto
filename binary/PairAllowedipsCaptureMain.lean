import PairAllowedipsCapture
open Lean Binary.Pair.Trie.Capture

def main (args : List String) : IO UInt32 := do
  let [inputPath,snapshotPath,layoutPath] := args
    | IO.eprintln "usage: binary-pair-allowedips-capture INPUT.json SNAPSHOT.json LAYOUTS.json"; return 1
  let .ok input := Json.parse (← IO.FS.readFile inputPath) >>= fromJson? (α := AllowedipsProbe.Input)
    | IO.eprintln "FAIL: invalid capture probe JSON"; return 1
  IO.eprintln "capture replay: parsing metadata"
  let .ok snapshot := Json.parse (← IO.FS.readFile snapshotPath) >>= fromJson? (α := Snapshot)
    | IO.eprintln "FAIL: invalid snapshot JSON"; return 1
  let .ok layout := Json.parse (← IO.FS.readFile layoutPath)
    | IO.eprintln "FAIL: invalid layout JSON"; return 1
  let mut bulk := #[]
  for block in snapshot.bulkBlocks do
    unless block.file != "" && block.file != "." && block.file != ".." && !block.file.contains '/' do
      IO.eprintln "FAIL: bulk capture filename must be local to snapshot directory"; return 1
    let bytes ← IO.FS.readBinFile ((System.FilePath.mk snapshotPath).parent.getD "." / block.file)
    unless bytes.size == block.size do IO.eprintln "FAIL: bulk capture has the wrong size"; return 1
    bulk := bulk.push (block.address,bytes)
  IO.eprintln "capture replay: loading Kraken memory"
  let memory := do loadBulk (← Binary.Pair.Capture.loadMemory snapshot.initial.blocks) bulk
  let .ok memory := memory | IO.eprintln "FAIL: invalid captured memory"; return 1
  IO.eprintln "capture replay: checking paired execution"
  let result := run input snapshot layout memory
  match result with
  | .ok report => IO.println report.compress; return 0
  | .error e => IO.eprintln s!"FAIL: {e}"; return 1
