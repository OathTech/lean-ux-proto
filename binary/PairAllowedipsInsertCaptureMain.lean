import PairAllowedipsInsertCapture
open Lean Binary.Pair.Allowedips.Capture

def main (args : List String) : IO UInt32 := do
  let [inputPath,snapshotPath] := args | IO.eprintln "usage: binary-allowedips-insert-capture INPUT SNAPSHOT"; return 1
  let input ← liftE (Json.parse (← IO.FS.readFile inputPath) >>= fromJson? (α := Binary.Pair.Allowedips.Input))
  let snapshot ← liftE (Json.parse (← IO.FS.readFile snapshotPath) >>= fromJson? (α := Snapshot))
  let mut bulk := #[]
  for block in snapshot.bulkBlocks do
    unless block.file != "" && block.file != "." && block.file != ".." && !block.file.contains '/' do
      IO.eprintln "FAIL: bulk capture filename must be local"; return 1
    let bytes ← IO.FS.readBinFile ((System.FilePath.mk snapshotPath).parent.getD "." / block.file)
    unless bytes.size == block.size do IO.eprintln "FAIL: bulk capture size"; return 1
    bulk := bulk.push (block.address,bytes)
  IO.eprintln "capture replay: loading actual memory"
  let memory ← liftE do Binary.Pair.Trie.Capture.loadBulk (← Binary.Pair.Capture.loadMemory snapshot.initial.blocks) bulk
  IO.eprintln "capture replay: executing paired insertion"
  match run input snapshot memory with
  | .error e => IO.eprintln s!"FAIL: {e}"; return 1
  | .ok result => IO.println result.compress; return 0
