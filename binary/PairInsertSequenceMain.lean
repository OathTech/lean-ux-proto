import PairInsertSequenceRunner
open Lean Leanux Leanux.WG Binary.Pair InsertSequence

def suite (input : ProbeInput) : Except String Json := do
  let recordedWorld ← replayRecordedPrefix input.trace input.operation
  let some d := recordedWorld.k.wg | throw "insert-sequence.recordedWorld.device"
  let [first,second] := d.peerList | throw "insert-sequence.recordedWorld.peers"
  unless d.indexTable.isEmpty && d.keypairs.isEmpty do throw "insert-sequence.recordedWorld.allocations"
  let some firstPeer := d.peers[first]? | throw "insert-sequence.recordedWorld.first-peer"
  let old (call : Sequence.Call) := Call.existing call
  let calls : List Call := [.insert (.handshake first),old (.lookup 7 [.handshake]),
    .insert (.handshake second),old (.replace first 20),old (.lookup 7 [.keypair]),
    old (.remove (.keypair 20)),old (.lookup 7 [.keypair]),.insert (.handshake first),
    .insert (.handshake second),old (.lookup 0 [.handshake]),old (.remove (.handshake first)),
    old (.remove (.handshake second)),old (.lookup 0 [.handshake])]
  let mut runs := #[]
  for collisions in [1,8,32] do
    let values := [7]++List.replicate collisions 7++[8199,8199,16391,0]
    let records := values.map fun value => Insert.record (.ofNat value)
    for dead in [false,true] do
      let dev := {d with
        peers := d.peers.insert first {firstPeer with refcount := if dead then 0 else firstPeer.refcount}
        keypairs := d.keypairs.insert 20 {peer := some first}}
      let world := {recordedWorld with k := {recordedWorld.k with wg := some dev},hidden := some records}
      for capacity in [coverageBytes/8,4] do
        for seed in [(0 : UInt64),0xffffffffffffffff] do
          for preempt in (if collisions==1 then [0,0xfffffe00] else [0]) do
            let report ← (runCalls input seed world calls capacity preempt).mapError
              (fun e => s!"collisions={collisions},dead={dead},capacity={capacity},preempt={preempt},seed={seed}: {e}")
            runs := runs.push (Json.mkObj [("collision_retries",toJson collisions),("dead_first_peer",toJson dead),
              ("initial_preempt",toJson preempt),("run",report)])
  return Json.mkObj [("status",toJson "pass"),
    ("origin",toJson "labelled synthetic mixed sequences derived from a recorded prefix; not captured uninterrupted kernel execution"),
    ("execution_scope",toJson "actual four anchors, callbacks and random-provider bodies; explicit caller installation"),
    ("controls",toJson ["missing input tape","private/output alias","nonzero nested pending word when read"]),
    ("calls_per_sequence",toJson calls.length),("runs",toJson runs)]

def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: binary-pair-insert-sequence INPUT.json"; return 1
  match (Json.parse (← IO.FS.readFile path) >>= fromJson? (α := ProbeInput)) >>= suite with
  | .ok report => IO.println report.compress; return 0
  | .error e => IO.eprintln s!"FAIL: {e}"; return 1
