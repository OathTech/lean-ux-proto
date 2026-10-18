import PairRemove
open Lean Leanux Leanux.WG Binary.Pair

def runCase (input : ProbeInput) (label : String) (w : World) (owners : List IndexOwner) : Except String Json := do
  let mut runs := #[]
  for seed in [(0 : UInt64),0xffffffffffffffff] do
    let mut s ← Remove.fixture input w
    let mut calls := #[]
    for owner in owners do
      let (next,report) ← (Remove.invoke input seed s owner).mapError (fun e => s!"{label}: {e}")
      s := next
      calls := calls.push report
    runs := runs.push (Json.mkObj [("seed",toJson seed.toNat),("calls",toJson calls)])
  return Json.mkObj [("case",toJson label),("runs",toJson runs)]

def suite (input : ProbeInput) : Except String Json := do
  let w ← replayRecordedPrefix input.trace input.operation
  let some d := w.k.wg | throw "remove prefix: no device"
  let [e] := d.indexTable | throw "remove pilot requires a one-entry recorded prefix"
  let .keypair kid := e.owner | throw "remove prefix: expected keypair owner"
  let [(pid,peer)] := d.peers.toList | throw "remove prefix: expected one peer"
  unless [peer.keypairNext,peer.keypairPrevious,peer.keypairCurrent].filterMap id == [kid] do
    throw "remove prefix: keypair-clear order differs"
  let some keypair := d.keypairs[kid]? | throw "remove prefix: missing keypair"
  unless keypair.refcount==1 do throw "remove prefix: keypair does not release"
  -- keypairsClear removes the keypair twice (unreference-now, then release);
  -- the peer's eventual release removes its handshake entry. Only the
  -- selected indexRemove calls execute here, not their intervening callers.
  let mut cases := #[← runCase input "recorded-prefix/selected-removal-calls" w
    [e.owner,e.owner,.handshake pid]]
  let mut collision := d
  let mut entries := []
  for i in [:3] do
    collision := {collision with keypairs := collision.keypairs.insert (100+i) {peer := some pid}}
    entries := entries ++ [⟨e.index+(i+1)*8192,.keypair (100+i)⟩]
  collision := {collision with indexTable := entries++[e]}
  let cw := {w with k := {w.k with wg := some collision}}
  for (label,order) in [("head-first",[IndexOwner.keypair 100,.keypair 101,.keypair 102,e.owner]),
      ("middle-first",[.keypair 101,e.owner,.keypair 100,.keypair 102]),
      ("tail-first",[e.owner,.keypair 102,.keypair 101,.keypair 100])] do
    cases := cases.push (← runCase input s!"synthetic/{label}" cw (order++order))
  -- An absent owner with a stale non-NULL pprev passes the lookup-only
  -- reconstruction. It can then unlink a different owner under removal.
  let spare := IndexOwner.keypair 999
  let badWorld := {w with k := {w.k with wg := some {d with keypairs := d.keypairs.insert 999 {peer := some pid}}}}
  let s ← Remove.fixture input badWorld
  let a ← addressOf s.names spare
  let bucketHead := s.names.table+(e.index%8192)*8
  let badMemory := put s.binary.state.data.dmem (a+input.offsets.hash+input.offsets.pprev) 8 bucketHead
  assertMemory s.names input.offsets badMemory badWorld
  let bad := {s with binary := {s.binary with state := {s.binary.state with data := {s.binary.state.data with dmem := badMemory}}}}
  let divergence ← match Remove.invoke input 0 bad spare false with
    | .ok _ => throw "stale-owner counterexample unexpectedly passed"
    | .error e =>
      unless (e.splitOn "bucket[").length>1 do throw s!"counterexample failed elsewhere: {e}"
      pure e
  let rejected ← match Remove.assertAt s.names input.offsets badMemory badWorld with
    | .ok _ => throw "new ownership assertion accepted stale pprev"
    | .error e =>
      unless e=="remove: owner hashed state differs" do throw s!"ownership failed elsewhere: {e}"
      pure e
  let some (_,peerBase) := s.names.peers.head? | throw "storage control: no registered peer"
  let aliases := {s.names with owners := s.names.owners ++ [(.keypair 1000,peerBase+input.offsets.peerRefcount)]}
  let storageRejected ← match Remove.assertAt aliases input.offsets s.binary.state.data.dmem s.world with
    | .ok _ => throw "storage control accepted a count/entry overlap"
    | .error e =>
      unless e=="remove: index storage overlaps or wraps" do throw s!"storage control failed elsewhere: {e}"
      pure e
  return Json.mkObj [("status",toJson "pass"),("entry_origin",toJson "recorded-prefix materialization and labelled synthetic heaps; not captured memory"),
    ("cases",toJson cases),("lookup_relation_counterexample",toJson divergence),("ownership_rejection",toJson rejected),
    ("storage_rejection",toJson storageRejected)]

def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: binary-pair-remove INPUT.json"; return 1
  let .ok input := Json.parse (← IO.FS.readFile path) >>= fromJson? (α := ProbeInput)
    | IO.eprintln "FAIL: invalid removal input"; return 1
  match suite input with
  | .ok report => IO.println report.compress; return 0
  | .error e => IO.eprintln s!"FAIL: {e}"; return 1
