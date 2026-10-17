import PairTrie
import AllowedipsSource
import PairLoopCheck
import PairTrieFrame

namespace Binary.Pair.Trie
open Lean Leanux Leanux.WG

def makeNames (d : Device) : Names :=
  ⟨d.nodes.toList.map (fun (id, _) => (id, AllowedipsProbe.nodeAddr id)),
    d.peers.toList.map (fun (id, _) => (id, peerAddr id))⟩

def advance (input : AllowedipsProbe.Input) (seed : UInt64) (r : Run)
    (stops : Array Nat) : Except String Run :=
  runUntil input.instructions input.labels input.hooks input.preempt r.state seed true
    input.budget input.entryPreempt stops (some r)

/-- Concrete caller check for the decoder-frame proof's separation premise.
This fixture has a 48-byte loop scratch area below its 80-byte caller frame.
Whole node allocations are protected, a conservative cover of decoder reads. -/
def loopSeparation (names : Names) (o : AllowedipsProbe.Offsets) : Except String Unit := do
  let spans := names.nodes.map (fun (_,a) => (a,o.nodeSize)) ++
    names.peers.map (fun (_,a) => (a+o.peerRefcount,4))
  for (a,size) in spans do
    unless a+size ≤ 2^64 && disjointRanges a size (stackAddr-128) 48 &&
        disjointRanges a size coverageAddr coverageBytes do throw "entry.loop-separation"

/-- Caller input condition, separate from reconstruction. A valid trie in
one family cannot be passed as the root of a lookup in the other family. -/
def callInput (names : Names) (o : AllowedipsProbe.Offsets) (memory : DataMem)
    (root : Option NodeId) (width key : Nat) : Except String Unit := do
  unless (width == 32 || width == 128) && key < 2^width do throw "entry.address-width"
  if let some id := root then
    let a ← address names.nodes (some id)
    let node ← (decodeNode names o memory a).mapError DecodeError.message
    unless node.width == width do throw "entry.root-family"

/-- Executable correspondence of the loop's live locals. The root and key
are call inputs, not values obtained from the expected successor. -/
def locals (names : Names) (input : AllowedipsProbe.Input) (s : MachineState)
    (root : Option NodeId) (width key : Nat) (current found : Option NodeId) : Except String Unit := do
  let regs := s.data.regs
  unless regs.rbx.toNat == (← address names.nodes current) do throw "loop.cursor"
  unless regs.rbp.toNat == (← address names.nodes found) do throw "loop.remembered"
  unless regs.rsp.toNat == stackAddr - 80 && regs.r12.toNat == width && regs.r13.toNat == width do
    throw "loop.stack/width"
  unless (← readNat s (stackAddr-72) 8) == (← address names.nodes root) do throw "loop.root"
  let actual : Nat ← if width == 32 then readNat s (stackAddr-64) 4 else do
    let hi ← readNat s (stackAddr-64) 8
    let lo ← readNat s (stackAddr-56) 8
    pure (hi * 2^64 + lo)
  unless actual == key do throw "loop.query"
  unless (← readNat s input.preempt 4) == (input.entryPreempt+512)%2^32 do throw "loop.preempt"

def assertHeader (names : Names) (input : AllowedipsProbe.Input) (r : Run)
    (w : World) (root : Option NodeId) (width key : Nat) (acc : AllowedipsSource.Acc) : Except String Unit := do
  assertAt names input.offsets r.state.data.dmem w
  unless r.state.pc.toBitVec.toNat == input.entry+0xd5 && acc.1.isNone && acc.2.1.isSome do
    throw "loop.header"
  locals names input r.state root width key acc.2.1 acc.2.2

def loopWrites (c : CommonBitsCoverage.Context) (s : MachineData) : List Span :=
  [((s.regs.rsp.toBitVec-48).toNat,48)] ++ writeSpans c

/-- The initial nonempty-loop boundary used by the symbolic sibling. Every
data premise is checked here; instruction and callback semantics are not tests. -/
def initialBoundary (names : Names) (input : AllowedipsProbe.Input)
    (c : CommonBitsCoverage.Context) (s : MachineState) (w : World)
    (root : Option NodeId) (width key : Nat) : Except String Unit := do
  assertAt names input.offsets s.data.dmem w
  callInput names input.offsets s.data.dmem root width key
  locals names input s root width key root none
  unless s.pc == AllowedipsImage.Lookup.entry+0xd5 && root.isSome do throw "boundary.header"
  unless frameCheck c s.data do throw "boundary.callback-frame"
  unless spansApart (decoderSpans names input.offsets) (loopWrites c s.data) do
    throw "boundary.decoder-separation"
  unless spansApart [((s.data.regs.rsp.toBitVec+16).toNat,width/8)] (loopWrites c s.data) do
    throw "boundary.query-separation"

/-- Metadata chosen by the synthetic materializer. initialBoundary checks it
against current memory; captured heaps will supply their decoded context. -/
def fixtureLoopContext (input : AllowedipsProbe.Input) : CommonBitsCoverage.Context :=
  ⟨⟨0x800000,.ofNat 64 coverageAddr,.ofNat 32 (coverageBytes/8),2,0⟩,
    .ofNat 32 (input.entryPreempt+512)⟩

def within (a bytes base size : Nat) : Bool := base ≤ a && a+bytes ≤ base+size

def footprint (names : Names) (input : AllowedipsProbe.Input) (width : Nat) (r : Run) : Except String Unit := do
  for (a, bytes) in r.writes do
    unless within a bytes (stackAddr-0x800) 0x800 || within a bytes coverageAddr coverageBytes ||
        within a bytes input.preempt 4 ||
        names.peers.any (fun (_, p) => within a bytes (p+input.offsets.peerRefcount) 4) do
      throw s!"write footprint: {bytes} at {a}"
  for (a, bytes) in r.reads do
    unless within a bytes (stackAddr-0x800) 0x810 || within a bytes coverageAddr coverageBytes ||
        within a bytes input.preempt 4 || within a bytes AllowedipsProbe.keyAddr (width/8) ||
        names.nodes.any (fun (_, p) => within a bytes p input.offsets.nodeSize) ||
        names.peers.any (fun (_, p) => within a bytes (p+input.offsets.peerRefcount) 4) ||
        within a bytes 0xffffffff81cc85c0 8 || within a bytes 0xffffffff81cc85e0 2 ||
        within a bytes (0x800000+0x6e0) 4 || within a bytes (0x800000+0x6e4) 4 ||
        within a bytes (0x800000+0x6e8) 8 || within a bytes (0x800000+0x704) 4 do
      throw s!"read footprint: {bytes} at {a}"

/-- Independent execution from one materialized entry. Each source iteration
is the existing proved presentation of the actual mirror. All callbacks and
common_bits execute as decoded instructions. Memory persists across calls. -/
def lookup (names : Names) (input : AllowedipsProbe.Input) (seed : UInt64)
    (memory : DataMem) (priorCoverage : Array Nat) (w : World)
    (root : Option NodeId) (width key : Nat) : Except String (World × Run × Json) := do
  assertAt names input.offsets memory w
  loopSeparation names input.offsets
  callInput names input.offsets memory root width key
  let regs : Reg64s := {
    rdi := .ofNat (← address names.nodes root), rsi := .ofNat width,
    rdx := .ofNat AllowedipsProbe.keyAddr, rsp := .ofNat stackAddr,
    rbx := 0x11, rbp := 0x22, r12 := 0x33, r13 := 0x44, r14 := 0x55, r15 := 0x66}
  let initial : MachineState := ⟨{regs, dmem := memory}, .ofNat input.entry⟩
  let stops := #[input.entry+0xd5, input.entry+0x101, input.entry+0x184]
  let mut r ← advance input seed {state := initial, history := #[initial], coverage := priorCoverage} stops
  if root.isSome then initialBoundary names input (fixtureLoopContext input) r.state w root width key
  let mut source := w
  let mut history := []
  let mut acc : AllowedipsSource.Acc := (none, root, none)
  let mut visits := 0
  let mut commonResults := #[]
  for occurrence in [:130] do
    let context := s!"iteration {occurrence}"
    if let some id := acc.2.1 then
      (assertHeader names input r source root width key acc).mapError (fun e => s!"{context}: {e}")
      let (node, _) ← (getNode id).run source |>.mapError Stop.message
      -- Stop after common_bits RET and compare its actual scalar effect.
      r ← advance input seed r #[input.entry+0xea]
      let common := AllowedipsSource.commonValue node key width
      unless r.state.pc.toBitVec.toNat == input.entry+0xea && r.state.data.regs.rax.toNat % 256 == common do
        throw s!"{context}: common_bits result"
      assertAt names input.offsets r.state.data.dmem source
      commonResults := commonResults.push common
      visits := visits+1
    let ((step, points), after) ← ((AllowedipsSource.iteration width key acc).run history).run source
      |>.mapError Stop.message
    let wasCurrent := acc.2.1
    if wasCurrent.isSome then r ← advance input seed r stops
    let next := match step with | .done a => a | .yield a => a
    if let some old := wasCurrent then
      if let .yield (_, some child, _) := step then
        let (n, _) ← (getNode old).run source |>.mapError Stop.message
        let (c, _) ← (getNode child).run after |>.mapError Stop.message
        unless n.cidr < c.cidr do throw s!"{context}: CIDR measure did not increase"
    source := after
    history := points
    acc := next
    assertAt names input.offsets r.state.data.dmem source
    let expectedPC := if acc.1.isNone && acc.2.1.isSome then input.entry+0xd5
      else if root.isNone then input.entry+0x184 else input.entry+0x101
    unless r.state.pc.toBitVec.toNat == expectedPC do throw s!"{context}: independent exits differ"
    unless root.isNone do
      unless r.state.data.regs.rbp.toNat == (← address names.nodes acc.2.2) do throw s!"{context}: exit.remembered"
    if acc.1.isSome then break
  let ((selected, _), finished) ← ((AllowedipsSource.finish acc).run history).run source |>.mapError Stop.message
  let (directSelected, directFind) ← (WG.findNode root width key).run w |>.mapError Stop.message
  unless selected == directSelected && finished.k == directFind.k && finished.steps == directFind.steps do
    throw "source loop adapter differs from findNode"
  let (answer, final) ← match (WG.lookup root width key).run w with
    | .ok result => pure result
    | .error e => do
      let .outsideDomain _ "lookup retry after a dying peer" := e |
        throw s!"source lookup refused: {e.message}"
      -- The mirror explicitly refuses a dying-peer retry. Execute the binary
      -- through its independent retry edge before reporting that refusal.
      let retry ← advance input seed r #[input.entry+0x74]
      unless retry.state.pc.toBitVec.toNat == input.entry+0x74 do throw "source refused without binary retry"
      footprint names input width retry
      throw s!"source refusal after binary retry ({retry.pcs.size} instructions): {e.message}"
  r ← advance input seed r #[]
  unless r.pcs.size ≤ input.budget do throw "whole-call instruction budget exhausted"
  assertAt names input.offsets r.state.data.dmem final
  unless r.state.pc.toBitVec.toNat == stopAddr && r.state.data.regs.rax.toNat == (← address names.peers answer) &&
      r.state.data.regs.rsp.toNat == stackAddr+8 do throw "return: result/PC/stack"
  for reg in [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15] do
    unless r.state.data.regs.get64 reg == initial.data.regs.get64 reg do throw "return: callee save"
  unless (← readNat r.state input.preempt 4) == input.entryPreempt do throw "return: preempt"
  unless (← readNat r.state 0xffffffff81cc85e0 2) == (← readNat initial 0xffffffff81cc85e0 2) do
    throw "return: pending softirq"
  unless (← readNat r.state coverageAddr 8) == r.coverage.size do throw "return: KCOV count"
  for i in [:r.coverage.size] do
    unless (← readNat r.state (coverageAddr+8*(i+1)) 8) == r.coverage[i]! do throw "return: KCOV word"
  footprint names input width r
  return (final, r, Json.mkObj [("headers", toJson visits), ("common_results", toJson commonResults),
    ("result", toJson answer), ("instructions", toJson r.pcs.size),
    ("reads", toJson r.reads.size), ("writes", toJson r.writes.size)])

end Binary.Pair.Trie
