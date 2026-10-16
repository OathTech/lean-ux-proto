import PairIndex

open Lean Leanux Leanux.WG Binary.Pair

def runCase (input : ProbeInput) (label : String) (w : World)
    (queries : List (Nat × List IndexKind)) : Except String Json := do
  let mut outcomes := #[]
  for seed in [(0 : UInt64), 0xffffffffffffffff] do
    let mut session ← startSession input w
    let mut calls := #[]
    for (query, kinds) in queries do
      let (next, report) ← (lookup input seed session query kinds).mapError
        (fun e => s!"{label}, seed {seed}: {e}")
      session := next
      calls := calls.push report
    outcomes := outcomes.push (Json.mkObj [("seed", toJson seed.toNat), ("calls", toJson calls)])
  return Json.mkObj [("case", toJson label), ("runs", toJson outcomes)]

def expectReject (label clause : String) (check : Except String Unit) : Except String Json := do
  match check with
  | .ok () => throw s!"negative control {label} was accepted"
  | .error e =>
    if (e.splitOn clause).length ≤ 1 then throw s!"negative control {label} failed for the wrong reason: {e}"
    return Json.mkObj [("control", toJson label), ("detected", toJson e)]

def suite (input : ProbeInput) : Except String Json := do
  let w ← replayPrefix input.trace input.operation
  let some d := w.k.wg | throw "prefix has no device"
  let [e] := d.indexTable | throw "pilot requires the one-entry recorded prefix"
  let .handshake pid := e.owner | throw "pilot prefix owner is not a handshake"
  let some peer := d.peers.get? pid | throw "pilot peer missing"
  let query := e.index
  let repeated := [(query, [.handshake]), (query, [.handshake])]
  let mut cases := #[]
  cases := cases.push (← runCase input "recorded-prefix/query" w [(input.query, [.handshake])])
  cases := cases.push (← runCase input "synthetic/empty-bucket" w [(query + 1, [.handshake])])
  cases := cases.push (← runCase input "synthetic/same-bucket-miss" w [(query + 8192, [.handshake])])
  cases := cases.push (← runCase input "synthetic/live-twice" w repeated)
  let dead := {w with k := {w.k with wg := some {d with peers := d.peers.insert pid {peer with refcount := 0}}}}
  cases := cases.push (← runCase input "synthetic/dead-twice" dead repeated)
  let null := {w with k := {w.k with wg := some {d with peers := d.peers.insert pid {peer with handshakeEntryPeer := none}}}}
  cases := cases.push (← runCase input "synthetic/null-twice" null repeated)
  -- Every colliding entry is embedded in a different keypair, but all of their
  -- peer words alias the same peer. These aliases must be accepted.
  for depth in [1, 3, 8] do
    let mut collision := d
    let mut entries := []
    for i in [:depth] do
      collision := {collision with keypairs := collision.keypairs.insert i {peer := some pid}}
      entries := entries ++ [⟨query + (i+1)*8192, .keypair i⟩]
    collision := {collision with indexTable := entries ++ [e]}
    let cw := {w with k := {w.k with wg := some collision}}
    cases := cases.push (← runCase input s!"synthetic/collisions-{depth}/live-twice" cw repeated)
    cases := cases.push (← runCase input s!"synthetic/collisions-{depth}/wrong-kind" cw
      [(query + 8192, [.handshake])])
    let cd := {cw with k := {cw.k with wg := some {collision with
      peers := collision.peers.insert pid {peer with refcount := 0}}}}
    cases := cases.push (← runCase input s!"synthetic/collisions-{depth}/keypair-dead-twice" cd
      [(query + 8192, [.keypair]), (query + 8192, [.keypair])])
  let base ← startSession input w
  let a ← addressOf base.names e.owner
  let m := base.binary.state.data.dmem
  let check (memory : DataMem) := assertMemory base.names input.offsets memory w
  let mut controls := #[]
  controls := controls.push (← expectReject "changed-refcount" "peer refcounts"
    (check (put m (peerAddr pid + input.offsets.peerRefcount) 4 (peer.refcount + 1))))
  controls := controls.push (← expectReject "cleared-owner" "owner peer words"
    (check (put m (a + input.offsets.peer) 8 0)))
  controls := controls.push (← expectReject "unresolved-peer" "unresolved peer pointer"
    (check (put m (a + input.offsets.peer) 8 0x123456)))
  controls := controls.push (← expectReject "cycle" "cycle"
    (check (put m (a + input.offsets.hash + input.offsets.next) 8 (a + input.offsets.hash))))
  controls := controls.push (← expectReject "backlink" "pprev"
    (check (put m (a + input.offsets.hash + input.offsets.pprev) 8 0)))
  controls := controls.push (← expectReject "wrong-kind" "kind disagrees"
    (check (put m (a + input.offsets.kind) 4 2)))
  controls := controls.push (← expectReject "missing-memory" "missing 8-byte range" (check {}))
  controls := controls.push (← expectReject "missing-owner-interpretation" "unresolved embedded entry"
    (assertMemory {base.names with owners := []} input.offsets m w))
  controls := controls.push (← expectReject "mapped-write-outside-footprint" "write footprint"
    (assertFootprint input base.names {base.binary with writes := #[(tableAddr, 8)]}))
  let crossing := a + input.offsets.entrySize - 1
  let mappedCrossing := {base.binary.state with data := {base.binary.state.data with dmem := put m crossing 8 0}}
  let _ ← readNat mappedCrossing crossing 8
  controls := controls.push (← expectReject "mapped-read-crosses-entry" "read footprint"
    (assertFootprint input base.names {base.binary with state := mappedCrossing, reads := #[(crossing, 8)]}))
  controls := controls.push (← expectReject "overlapping-allocation" "separation"
    (assertMemory {base.names with table := peerAddr pid} input.offsets m w))
  controls := controls.push (← expectReject "missing-label" "missing label"
    ((advance {input with labels := #[]} 0 base.binary #[]).map (fun _ => ())))
  let regs : Reg64s := {
    rdi := .ofNat tableAddr, rsi := 1, rdx := .ofNat query,
    rcx := .ofNat outputAddr, rsp := .ofNat stackAddr}
  let initial : MachineState := ⟨{base.binary.state.data with regs}, Binary.Image.Lookup.entry⟩
  let atHeader ← advance input 0 {state := initial} #[header]
  let paired := {base with binary := atHeader}
  assertHeader input paired query [.handshake] [e]
  let wrongCursor := {atHeader with state := {atHeader.state with data := {atHeader.state.data with
    regs := {atHeader.state.data.regs with rbx := 0}}}}
  controls := controls.push (← expectReject "loop-cursor" "loop.cursor"
    (assertHeader input {paired with binary := wrongCursor} query [.handshake] [e]))
  controls := controls.push (← expectReject "loop-query" "loop.saved-locals"
    (assertHeader input paired (query + 8192) [.handshake] [e]))
  controls := controls.push (← expectReject "loop-remaining" "loop.remaining"
    (assertHeader input paired query [.handshake] [e, e]))
  return Json.mkObj [("status", toJson "pass"),
    ("entry_origin", toJson "materialized recorded prefix plus labelled synthetic mutations; no captured kernel heap"),
    ("services", toJson "decoded bodies; no callback summaries"),
    ("cases", toJson cases), ("negative_controls", toJson controls)]

def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: binary-pair-runner INPUT.json"; return 1
  let parsed := Json.parse (← IO.FS.readFile path) >>= fromJson? (α := ProbeInput)
  match parsed >>= suite with
  | .ok result => IO.println result.compress; return 0
  | .error e => IO.eprintln s!"FAIL: {e}"; return 1
