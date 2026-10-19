import SourceAdapter
import PairSequenceRunner
open Lean Leanux Leanux.WG Binary.Pair Sequence

def suite (input : ProbeInput) : Except String Json := do
  let w ← replayRecordedPrefix input.trace input.operation
  let some d := w.wg.dev | throw "sequence.prefix.device"
  let [e] := d.indexTable | throw "sequence.prefix.index-entry"
  let .keypair kid := e.owner | throw "sequence.prefix.keypair"
  let [(pid,peer)] := d.peers.toList | throw "sequence.prefix.peer"
  let old : IndexEntry := {e with owner := .handshake pid}
  let mut collision := {d with indexTable := []}
  let mut neighbors := []
  for i in [:3] do
    collision := {collision with keypairs := collision.keypairs.insert (100+i) {peer := some pid}}
    neighbors := neighbors ++ [⟨e.index+(i+1)*8192,.keypair (100+i)⟩]
  collision := {collision with indexTable := neighbors.take 1++[old]++neighbors.drop 1}
  let calls : List Call := [.lookup e.index [.handshake],.replace pid kid,
    .lookup e.index [.handshake],.lookup e.index [.keypair],.replace pid kid,
    .remove (.keypair kid),.remove (.keypair kid),.lookup e.index [.keypair],
    .lookup (e.index+8192) [.keypair],.remove (.handshake pid)]
  let mut runs := #[]
  for dead in [false,true] do
    let dev := if dead then {collision with peers := collision.peers.insert pid {peer with refcount := 0}} else collision
    let world := {w with wg := {w.wg with dev := some dev}}
    for capacity in [coverageBytes/8,4] do
      for seed in [(0 : UInt64),0xffffffffffffffff] do
        let report ← (runCalls input seed world calls capacity).mapError
          (fun e => s!"dead={dead}, capacity={capacity}, seed={seed}: {e}")
        runs := runs.push (Json.mkObj [("dead",toJson dead),("run",report)])
  return Json.mkObj [("status",toJson "pass"),
    ("origin",toJson "synthetic mixed sequences built from a recorded-prefix projection; not captured uninterrupted kernel execution"),
    ("calls_per_sequence",toJson calls.length),("runs",toJson runs)]

def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: binary-pair-sequence INPUT.json"; return 1
  match (Json.parse (← IO.FS.readFile path) >>= fromJson? (α := ProbeInput)) >>= suite with
  | .ok report => IO.println report.compress; return 0
  | .error e => IO.eprintln s!"FAIL: {e}"; return 1
