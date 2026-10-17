import PairAllowedips

open Lean Leanux Leanux.WG Binary.Pair.Trie

def expectReject (label clause : String) (check : Except String Unit) : Except String Json := do
  match check with
  | .ok () => throw s!"control {label} was accepted"
  | .error e =>
    unless (e.splitOn clause).length > 1 do throw s!"control {label} failed for the wrong reason: {e}"
    return Json.mkObj [("control", toJson label), ("detected", toJson e)]

def runCase (input : AllowedipsProbe.Input) (label : String) (w : World)
    (root : Option NodeId) (width key : Nat) (calls : Nat := 1) : Except String Json := do
  let some d := w.k.wg | throw "missing device"
  let names := makeNames d
  let memory ← AllowedipsProbe.materialize d input.offsets key width input.preempt input.entryPreempt
  let mut outcomes := #[]
  for seed in [(0 : UInt64), 0xffffffffffffffff] do
    let mut nextWorld := w
    let mut nextMemory := memory
    let mut coverage := #[]
    let mut reports := #[]
    for call in [:calls] do
      let (after, r, report) ← (lookup names input seed nextMemory coverage nextWorld root width key).mapError
        (fun e => s!"{label}, seed {seed}, call {call}: {e}")
      nextWorld := after
      nextMemory := r.state.data.dmem
      coverage := r.coverage
      reports := reports.push report
    outcomes := outcomes.push (Json.mkObj [("seed", toJson seed.toNat), ("calls", toJson reports)])
  return Json.mkObj [("case", toJson label), ("runs", toJson outcomes)]

def withNodes (w : World) (d : Device) (width : Nat) (nodes : List (NodeId × AipNode))
    (root : Option NodeId) : World :=
  let nodes := nodes.foldl (fun m (id,n) => m.insert id n) ({} : Std.TreeMap NodeId AipNode)
  let device := {d with nodes, peerAllowedips := {
    root4 := if width == 32 then root else none
    root6 := if width == 128 then root else none}}
  {w with k := {w.k with wg := some device}}

def suite (input : AllowedipsProbe.Input) : Except String Json := do
  let trace ← Leanux.Runner.parseTrace input.trace
  let some (.wgXmit family key _ _) := trace.ops[input.operation]? | throw "expected wg_xmit"
  let prior ← replayRecordedPrefix input.trace input.operation
  let w := {prior with steps := #[], hidden := some [], netRxSection := 0, netRxSections := 0}
  let some d := w.k.wg | throw "prefix device missing"
  let width := if family == 4 then 32 else 128
  let root := if width == 32 then d.peerAllowedips.root4 else d.peerAllowedips.root6
  let some (pid, peer) := d.peers.toList.head? | throw "prefix has no peer"
  let mut cases := #[]
  cases := cases.push (← runCase input "recorded-prefix/live-twice" w root width key 2)
  let empty := withNodes w d width [] none
  cases := cases.push (← runCase input "synthetic/empty-root" empty none width key)
  let full := newNode key width width (some pid)
  let fullWorld := withNodes w d width [(0,full)] (some 0)
  cases := cases.push (← runCase input "synthetic/full-prefix" fullWorld (some 0) width key)
  cases := cases.push (← runCase input "synthetic/prefix-mismatch" fullWorld (some 0) width (key ^^^ 1))
  let short := newNode key 0 width (some pid)
  let absent := withNodes w d width [(0,short)] (some 0)
  cases := cases.push (← runCase input "synthetic/absent-child-remembered" absent (some 0) width key)
  let peerless := withNodes w d width [(0,{short with peer := none})] (some 0)
  cases := cases.push (← runCase input "synthetic/absent-child-miss" peerless (some 0) width key)
  for depth in [2,8,32] do
    let mut nodes := []
    for i in [:depth] do
      let cidr := i * (width / depth)
      let side := key / 2^(width-1-cidr) % 2
      let children := #[none,none] |>.set! side (if i+1 < depth then some (i+1) else none)
      let n := {newNode key cidr width (if i == 0 then some pid else none) with bit := children}
      nodes := nodes ++ [(i,n)]
    let deep := withNodes w d width nodes (some 0)
    cases := cases.push (← runCase input s!"synthetic/depth-{depth}-remembered" deep (some 0) width key)
  -- Same high IPv6 word, different low word; the recorded route also exercises
  -- high-word differences. IPv4 exercises the 32-bit path.
  if width == 128 then
    cases := cases.push (← runCase input "synthetic/ipv6-low-word-mismatch" fullWorld (some 0) width (key ^^^ 2^32))
  let some fd := fullWorld.k.wg | throw "full fixture device missing"
  let dead := {fullWorld with k := {fullWorld.k with wg := some {fd with peers := fd.peers.insert pid {peer with refcount := 0}}}}
  let refusal ← expectReject "dying-peer-is-explicit-refusal" "lookup retry after a dying peer"
    ((runCase input "synthetic/dead-peer" dead (some 0) width key).map (fun _ => ()))
  let names := makeNames fd
  let m ← AllowedipsProbe.materialize fd input.offsets key width input.preempt input.entryPreempt
  let check := fun memory => assertAt names input.offsets memory fullWorld
  let a := AllowedipsProbe.nodeAddr 0
  let mut controls := #[refusal]
  controls := controls.push (← expectReject "selector" "node.selectors" (check (put m (a+input.offsets.bitAtB) 1 8)))
  controls := controls.push (← expectReject "unresolved-child" "unresolved pointer" (check (put m (a+input.offsets.children) 8 42)))
  controls := controls.push (← expectReject "missing-memory" "missing 8-byte range" (check {}))
  controls := controls.push (← expectReject "peer-count" "trie.counts" (check (put m (peerAddr pid+input.offsets.peerRefcount) 4 99)))
  controls := controls.push (← expectReject "key" "trie.nodes" (check (put m (a+input.offsets.bits) 4 99)))
  controls := controls.push (← expectReject "missing-identity" "trie.nodes"
    (assertAt {names with nodes := []} input.offsets m fullWorld))
  let cycle := withNodes w d width [(0,{short with bit := #[some 0,none]})] (some 0)
  controls := controls.push (← expectReject "cycle" "trie.parents"
    ((runCase input "cycle" cycle (some 0) width key).map (fun _ => ())))
  let sm ← AllowedipsProbe.materialize fd input.offsets key width input.preempt input.entryPreempt
  let regs : Reg64s := {rdi := .ofNat a, rsi := .ofNat width, rdx := .ofNat AllowedipsProbe.keyAddr, rsp := .ofNat stackAddr}
  let atHeader ← advance input 0 {state := ⟨{regs, dmem := sm}, .ofNat input.entry⟩} #[input.entry+0xd5]
  let checkHeader := fun r => assertHeader names input r fullWorld (some 0) width key (none,some 0,none)
  checkHeader atHeader
  let changeRegs := fun regs => {atHeader with state := {atHeader.state with data := {atHeader.state.data with regs}}}
  controls := controls.push (← expectReject "cursor" "loop.cursor" (checkHeader (changeRegs {atHeader.state.data.regs with rbx := 0})))
  controls := controls.push (← expectReject "remembered" "loop.remembered" (checkHeader (changeRegs {atHeader.state.data.regs with rbp := .ofNat a})))
  controls := controls.push (← expectReject "query" "loop.query"
    (assertHeader names input atHeader fullWorld (some 0) width (key ^^^ 1) (none,some 0,none)))
  controls := controls.push (← expectReject "mapped-write-to-trie" "write footprint"
    (footprint names input width {atHeader with writes := #[(a,8)]}))
  return Json.mkObj [("status", toJson "pass"), ("width", toJson width),
    ("entry_origin", toJson "recorded source prefixes and labelled synthetic variations; materialized memory, not captured kernel states"),
    ("cases", toJson cases), ("controls", toJson controls)]

def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: binary-pair-allowedips INPUT.json"; return 1
  let parsed := Json.parse (← IO.FS.readFile path) >>= fromJson? (α := AllowedipsProbe.Input)
  match parsed >>= suite with
  | .ok result => IO.println result.compress; return 0
  | .error e => IO.eprintln s!"FAIL: {e}"; return 1
