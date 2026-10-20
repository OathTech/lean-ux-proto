import PairInsertWitnessState
import PairInsertProvider

open Lean Leanux Leanux.WG Binary Binary.Pair

def witnessOffsetWords (o : Offsets) : List Nat :=
  [o.tableSize,o.buckets,o.headSize,o.first,o.entrySize,o.peer,o.hash,o.next,o.pprev,
    o.kind,o.index,o.peerHandshake,o.handshakeEntry,o.keypairEntry,o.peerRefcount]

def runWitnesses (input : ProbeInput) : Except String Json := do
  unless witnessOffsetWords input.offsets==witnessOffsetWords Insert.Witness.offsets do
    throw "insert witness layout differs from image-derived input"
  let mut results := #[]
  for linked in [false,true] do
    for seed in [(0 : UInt64),0xffffffffffffffff] do
      let initial := Insert.Witness.state linked
      Insert.callBoundary Insert.Witness.names Insert.Witness.offsets Insert.Witness.context initial
        (Insert.Witness.world linked) (.keypair 0) (.ofNat stopAddr)
      Insert.providerCheck Insert.Witness.names Insert.Witness.offsets Insert.Witness.context initial
        (.ofNat stopAddr) Insert.Witness.config
      let s : Session := {names := Insert.Witness.names,world := Insert.Witness.world linked,binary := {state := initial}}
      let random (_ordinal : Nat) (r : Run) (value : Nat) : Except String Run := do
        let c ← Index.readContext r.state.data.dmem
        RandomProvider.readyCheck Insert.Witness.config c r.state
        let after ← RandomRun.execute seed 20000 r.state (.ofNat (Insert.entry+0x79))
        RandomRun.physicalPost Insert.Witness.config c r.state after (.ofNat (Insert.entry+0x79))
        unless after.state.data.regs.rax.toNat==value do throw "insert.witness.draw"
        return {r with
          state := after.state,pcs := r.pcs++after.pcs,
          reads := r.reads++after.reads,writes := r.writes++after.writes,
          undefinedCount := r.undefinedCount+after.undefinedCount}
      let (after,report) ← Insert.invokeFrom input seed s (.keypair 0) initial {} random
        "actual decoded initialized provider from the exact Lean witness state" Insert.Witness.config.blocks
      unless after.world.hidden==some [] do throw "insert.witness.input"
      results := results.push (Json.mkObj [("initially_linked",toJson linked),("seed",toJson seed.toNat),("call",report)])
  return Json.mkObj [("status",toJson "pass"),("origin",toJson "synthetic exact Lean witness states"),
    ("execution_scope",toJson "actual insertion, callbacks and initialized random-provider body"),("runs",toJson results)]

def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: binary-pair-insert-witness INPUT.json"; return 1
  let input := Json.parse (← IO.FS.readFile path) >>= fromJson? (α := ProbeInput)
  match input >>= runWitnesses with
  | .ok report => IO.println report.compress; return 0
  | .error e => IO.eprintln s!"FAIL: {e}"; return 1
