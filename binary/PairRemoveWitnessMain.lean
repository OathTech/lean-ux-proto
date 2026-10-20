import PairRemoveWitnessState

open Lean Leanux Leanux.WG Binary Binary.Pair

def offsetWords (o : Offsets) : List Nat :=
  [o.tableSize,o.buckets,o.headSize,o.first,o.entrySize,o.peer,o.hash,o.next,o.pprev,
    o.kind,o.index,o.peerHandshake,o.handshakeEntry,o.keypairEntry,o.peerRefcount]

def runWitnesses (input : ProbeInput) : Except String Json := do
  unless offsetWords input.offsets==offsetWords Remove.Witness.offsets do
    throw "witness layout differs from image-derived input"
  let mut reports := #[]
  for linked in [false,true] do
    for seed in [(0 : UInt64),0xffffffffffffffff] do
      let s : Session := {names := Remove.Witness.names,world := Remove.Witness.world linked,binary := {state := Remove.Witness.state linked}}
      let (next,report) ← Remove.invoke input seed s (.keypair 0)
      let (_,repeatReport) ← Remove.invoke input seed next (.keypair 0)
      reports := reports.push (Json.mkObj [("initially_linked",toJson linked),("seed",toJson seed.toNat),
        ("call",report),("repeated_call",repeatReport)])
  let initial := Remove.Witness.state false
  let bad := {initial with data := {initial.data with dmem := put initial.data.dmem TrustBase.preemptCountAddress.toNat 4 0x10000}}
  let context ← Index.readContext bad.data.dmem
  let rejected ← match Remove.callBoundary Remove.Witness.names input.offsets context bad
      (Remove.Witness.world false) (.keypair 0) (.ofNat stopAddr) with
    | .ok () => throw "entry control accepted a hardirq preempt count"
    | .error error =>
      unless error=="index.call.hardirq" do throw s!"entry control failed elsewhere: {error}"
      pure error
  return Json.mkObj [("status",toJson "pass"),("origin",toJson "synthetic exact Lean witness states"),
    ("runs",toJson reports),("hardirq_rejection",toJson rejected)]

def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: binary-pair-remove-witness INPUT.json"; return 1
  let input := Json.parse (← IO.FS.readFile path) >>= fromJson? (α := ProbeInput)
  match input >>= runWitnesses with
  | .ok report => IO.println report.compress; return 0
  | .error e => IO.eprintln s!"FAIL: {e}"; return 1
