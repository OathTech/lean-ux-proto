import PairReplace
open Lean Leanux Leanux.WG Binary.Pair

def runCase (input : ProbeInput) (label : String) (w : World) (pid : PeerId)
    (kid : KeypairId) : Except String Json := do
  let mut runs := #[]
  for seed in [(0 : UInt64),0xffffffffffffffff] do
    let mut s ← Replace.fixture input w
    let mut calls := #[]
    for _ in [:2] do
      let (next,report) ← (Replace.invoke input seed s pid kid).mapError (fun e => s!"{label}: {e}")
      s := next
      calls := calls.push report
    runs := runs.push (Json.mkObj [("seed",toJson seed.toNat),("calls",toJson calls)])
  return Json.mkObj [("case",toJson label),("runs",toJson runs)]

def suite (input : ProbeInput) : Except String Json := do
  let w ← replayRecordedPrefix input.trace input.operation
  let some d := w.k.wg | throw "replace prefix: no device"
  let [e] := d.indexTable | throw "replace pilot requires a one-entry recorded prefix"
  let .keypair kid := e.owner | throw "replace prefix: expected keypair owner"
  let [(pid,_)] := d.peers.toList | throw "replace prefix: expected one peer"
  -- Reconstruct only the pre-replacement index projection from the completed
  -- recorded operation. This is explicitly not a captured entry World.
  let old : IndexEntry := {e with owner := .handshake pid}
  let before := {d with indexTable := [old]}
  let bw := {w with k := {w.k with wg := some before}}
  let mut cases := #[← runCase input "record-derived/projection-before-replacement" bw pid kid]
  cases := cases.push (← runCase input "synthetic/failure-new-already-linked" w pid kid)
  let mut collision := before
  let mut entries := []
  for i in [:3] do
    collision := {collision with keypairs := collision.keypairs.insert (100+i) {peer := some pid}}
    entries := entries ++ [⟨e.index+(i+1)*8192,.keypair (100+i)⟩]
  for (label,table) in [("head",old::entries),("middle",entries.take 1++[old]++entries.drop 1),
      ("tail",entries++[old])] do
    let cw := {w with k := {w.k with wg := some {collision with indexTable := table}}}
    cases := cases.push (← runCase input s!"synthetic/{label}" cw pid kid)
  let some keypair := before.keypairs[kid]? | throw "replace target missing"
  let independent := {before with keypairs := before.keypairs.insert kid {keypair with peer := none}}
  cases := cases.push (← runCase input "synthetic/independent-null-new-peer-word"
    {bw with k := {bw.k with wg := some independent}} pid kid)
  let s ← Replace.fixture input bw
  let new ← addressOf s.names (.keypair kid)
  let badMemory := put s.binary.state.data.dmem (new+input.offsets.kind) 4 1
  -- Lookup-only reconstruction does not read an unlinked owner's kind.
  Remove.assertAt s.names input.offsets badMemory bw
  let bad := {s with binary := {s.binary with state := {s.binary.state with data := {s.binary.state.data with dmem := badMemory}}}}
  let rejected ← match Replace.invoke input 0 bad pid kid with
    | .ok _ => throw "replace kind control accepted a handshake-kind keypair"
    | .error e =>
      unless e=="replace.call.new-kind" do throw s!"replace kind control failed elsewhere: {e}"
      pure e
  return Json.mkObj [("status",toJson "pass"),("entry_origin",toJson "record-derived index projection and labelled synthetic heaps; not captured entry memory or World"),
    ("cases",toJson cases),("new_kind_rejection",toJson rejected)]

def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: binary-pair-replace INPUT.json"; return 1
  let .ok input := Json.parse (← IO.FS.readFile path) >>= fromJson? (α := ProbeInput)
    | IO.eprintln "FAIL: invalid replacement input"; return 1
  match suite input with
  | .ok report => IO.println report.compress; return 0
  | .error e => IO.eprintln s!"FAIL: {e}"; return 1
