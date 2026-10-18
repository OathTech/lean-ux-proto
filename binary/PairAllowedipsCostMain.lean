import PairAllowedipsCapture
open Lean Leanux Binary.Pair Binary.Pair.Trie

/-- Diagnostic generated variation: keep the captured prefix of KCOV bytes
but reduce capacity and its task metadata. This is explicitly not replay of
an unchanged kernel snapshot. The shared call assertion still checks every
byte required by the smaller allocation. -/
def main (args : List String) : IO UInt32 := do
  let [inputPath,snapshotPath,layoutPath] := args
    | IO.eprintln "usage: binary-pair-buffer-cost INPUT.json SNAPSHOT.json LAYOUT.json"; return 1
  let input : AllowedipsProbe.Input ← liftE (Json.parse (← IO.FS.readFile inputPath) >>= fromJson?)
  let snapshot : Binary.Pair.Trie.Capture.Snapshot ← liftE (Json.parse (← IO.FS.readFile snapshotPath) >>= fromJson?)
  let layout ← liftE (Json.parse (← IO.FS.readFile layoutPath))
  let words := snapshot.initial.coverageUsed+4096
  unless words < snapshot.initial.capacity do throw (IO.userError "benchmark requires a smaller generated allocation")
  let started ← IO.monoMsNow
  let mut memory ← liftE (Binary.Pair.Capture.loadMemory snapshot.initial.blocks)
  for block in snapshot.bulkBlocks do
    unless block.address==snapshot.initial.coverage && block.file != "" && block.file != "." && block.file != ".." && !block.file.contains '/' do
      throw (IO.userError "benchmark requires one local coverage block")
    let raw ← IO.FS.readBinFile ((System.FilePath.mk snapshotPath).parent.getD "." / block.file)
    unless raw.size==block.size && 8*words≤raw.size do throw (IO.userError "benchmark bulk size differs")
    memory ← liftE (Binary.Pair.Trie.Capture.loadBulk memory #[(block.address,raw.extract 0 (8*words))])
  memory := put memory (snapshot.initial.task+0x6e4) 4 words
  let snapshot := {snapshot with initial := {snapshot.initial with capacity := words,coverageCapturedWords := words}}
  let initial ← liftE (snapshot.initial.registers.state memory)
  let prior ← liftE (replayRecordedPrefix input.trace input.operation)
  let w := {prior with steps := #[],hidden := some [],netRxSection := 0,netRxSections := 0}
  let some d := w.k.wg | throw (IO.userError "benchmark prefix has no device")
  let trace ← liftE (Runner.parseTrace input.trace)
  let some (.wgXmit family key _ _) := trace.ops[input.operation]? | throw (IO.userError "benchmark operation differs")
  let bits := if family==4 then 32 else 128
  let root := if bits==32 then d.peerAllowedips.root4 else d.peerAllowedips.root6
  let names ← liftE (Binary.Pair.Trie.Capture.names input snapshot layout initial d)
  let (frame,coverage) ← liftE (Binary.Pair.Trie.Capture.frame input snapshot layout initial)
  let input := {input with entryPreempt := frame.entryPreempt,budget := frame.budget}
  let mut records := #[]
  for i in [:snapshot.initial.coverageUsed] do
    records := records.push (← liftE (readNat initial (frame.coverage+8*(i+1)) 8))
  let mut runs := #[]
  for seed in [(0 : UInt64),0xffffffffffffffff] do
    let (_,result,report) ← liftE (lookupFrom names input seed initial frame coverage records w root bits key)
    unless result.pcs==snapshot.executedPCs do throw (IO.userError "smaller-buffer instruction path differs")
    runs := runs.push report
  let finished ← IO.monoMsNow
  IO.println (Json.mkObj [("status",toJson "pass"),("origin",toJson "generated smaller-buffer variation; not unchanged captured replay"),
    ("capacity_words",toJson words),("elapsed_ms",toJson (finished-started)),("runs",toJson runs)]).compress
  return 0
