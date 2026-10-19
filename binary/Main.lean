import SourceAdapter
import ProbeSupport
import AllowedipsFixture
import LookupObservation
import TrustBase

open Lean Binary

def probe (input : ProbeInput) (actualServices : Bool := false) : Except String Json := do
  let w ← replayPrefix input.trace input.operation
  let some dev := w.wg.dev | throw "no device after prefix"
  unless dev.indexTable.length == 1 do throw "expected one entry after recorded prefix"
  let before := dev.indexTable
  let (answer, after) ← (Source.indexLookup [.handshake] input.query).run w
    |>.mapError Leanux.Stop.message
  let some afterDev := after.wg.dev | throw "mirror lost device"
  let memory ← materializePeers dev input.offsets (← materialize dev input.offsets input.preempt)
  let memory := put memory Binary.Layouts.keypairCounterAddress.toNat 8 w.wg.keypairCounter
  let memory := if actualServices then materializeServices memory else memory
  let some entry := input.instructions[0]? | throw "empty instruction list"
  let regs : Reg64s := {
    rdi := .ofNat tableAddr
    rsi := 1
    rdx := .ofNat input.query
    rcx := .ofNat outputAddr
    rsp := .ofNat stackAddr
    rbx := 0x11, rbp := 0x22, r12 := 0x33, r13 := 0x44, r14 := 0x55, r15 := 0x66 }
  let initial : MachineState := ⟨{regs, dmem := memory}, .ofNat entry.pc⟩
  let r ← runMachine input initial 0 actualServices
  let alternate ← runMachine input initial 0xffffffffffffffff actualServices
  unless r.coverage == alternate.coverage && r.pcs == alternate.pcs && r.state.data.regs == alternate.state.data.regs &&
      r.state.data.dmem == alternate.state.data.dmem do throw "undefined-value seed changes observables"
  let answerAddr ← match answer with
    | none => pure 0
    | some (owner, _) => do
      let some e := before.find? (·.owner == owner) | throw "returned owner is not in initial table"
      entryAddr e input.offsets
  unless r.state.data.regs.rax.toNat == answerAddr && r.state.data.regs.rsp.toNat == stackAddr + 8 do
    throw "return or stack mismatch"
  for reg in [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15] do
    unless r.state.data.regs.get64 reg == initial.data.regs.get64 reg do throw s!"callee-save mismatch: {repr reg}"
  let stackBase := BitVec.ofNat 64 (stackAddr - 0x800)
  let some stackBytes := memory.loadBytes stackBase 0x810 | throw "initial stack missing"
  let expected ← materializePeers afterDev input.offsets (← materialize afterDev input.offsets input.preempt)
  let expected := match answer with
    | none => expected
    | some (_, pid) => put expected outputAddr 8 (peerAddr pid)
  let expected := put expected Binary.Layouts.keypairCounterAddress.toNat 8 after.wg.keypairCounter
  let expected := if actualServices then materializeServices expected else expected
  let mut finalMemory := r.state.data.dmem.storeBytes stackBase stackBytes
  if actualServices then
    unless (← readNat r.state coverageAddr 8) == r.coverage.size do
      throw "actual KCOV count differs from reached callback count"
    for i in [:r.coverage.size] do
      unless (← readNat r.state (coverageAddr + 8 * (i+1)) 8) == r.coverage[i]! do
        throw "actual KCOV buffer differs from callback return addresses"
    finalMemory := finalMemory.storeBytes (.ofNat 64 coverageAddr) (List.replicate coverageBytes 0)
  unless finalMemory == expected do
    throw "non-stack memory disagrees with mirror"
  -- Exercise the proof-side observer on every concrete instruction state.
  -- This checks its event ordering, not the unfinished physical relation R.
  let observed ← Binary.LookupObservation.observe w.netRxSection r.history.toList
  let decisions := (observed.filterMap (·.step)).toArray.map Leanux.Step.label
  let ((loggedAnswer, points), _) ← ((Binary.MirrorHistory.lookup [.handshake] input.query).run []).run w
    |>.mapError Leanux.Stop.message
  unless loggedAnswer == answer do throw "logged mirror changed lookup's result"
  unless observed.length == points.length do
    throw s!"correspondence length mismatch: machine={observed.length}, mirror={points.length}"
  for (actual, expectedPoint) in observed.zip points do
    unless actual.tag == expectedPoint.tag do
      throw s!"correspondence tag mismatch: {repr actual.tag} versus {repr expectedPoint.tag}"
    if let some step := actual.step then
      unless expectedPoint.world.steps.back? == some step do
        throw s!"correspondence decision mismatch: {Leanux.Step.label step}"
  let mirrorDecisions := after.steps.map Leanux.Step.label
  unless decisions == mirrorDecisions do throw s!"decision disagreement: machine={decisions}, mirror={mirrorDecisions}"
  return Json.mkObj [
    ("status", toJson "pass"), ("result", toJson (if answer.isSome then "entry/peer" else "none/null")),
    ("services", toJson (if actualServices then "decoded bodies, KCOV_TRACE_PC" else "summaries")),
    ("instructions_executed", toJson r.pcs.size), ("coverage", toJson r.coverage),
    ("comparisons", toJson r.comparisons), ("decisions", toJson decisions),
    ("mirror_decisions", toJson mirrorDecisions), ("correspondence_points", toJson observed.length), ("memory", toJson "all non-stack bytes match materialized mirror result"),
    ("entries", toJson (before.map fun e => e.index)), ("query", toJson input.query),
    ("undefined_choices", toJson r.undefinedCount), ("write_accesses", toJson r.writes)]

/-- Synthetic accepted mirror state, not claimed to be a reachable kernel
    entry. Execute the real decoded callee as well as lookup, twice. -/
def deadPeerCounterexample (input : ProbeInput) (keypairCase : Bool := false) : Except String Json := do
  let w ← replayPrefix input.trace input.operation
  let some dev := w.wg.dev | throw "no device"
  let [e] := dev.indexTable | throw "requires the single-entry fixture"
  let some pid ← ownerWord dev e.owner | throw "fixture peer word already NULL"
  let e := if keypairCase then {e with owner := .keypair 0} else e
  let dev := if keypairCase then
      {dev with
        indexTable := [e]
        keypairs := dev.keypairs.insert 0 {peer := some pid}}
    else dev
  let some peer := dev.peers.get? pid | throw "missing peer"
  let w := {w with wg := { w.wg with dev := some { dev with
    peers := dev.peers.insert pid {peer with refcount := 0} } }, ambient := {w.ambient with steps := #[]}}
  let (answer1, after1) ← (Source.indexLookup [e.kind] e.index).run w
    |>.mapError Leanux.Stop.message
  let (answer2, after2) ← (Source.indexLookup [e.kind] e.index).run {after1 with ambient := {after1.ambient with steps := #[]}}
    |>.mapError Leanux.Stop.message
  unless answer1.isNone && answer2.isNone && after2.wg.dev == after1.wg.dev do
    throw "dead-peer lookup result or second owner store differs"
  let some afterDev := after1.wg.dev | throw "device disappeared"
  unless (← ownerWord afterDev e.owner).isNone do throw "mirror did not clear owning peer word"
  let memory ← materialize dev input.offsets input.preempt
  let memory ← materializePeers dev input.offsets memory
  let peerAddress := peerAddr pid
  let memory := put memory (peerAddress + input.offsets.peerRefcount) 4 0
  let some entry := input.instructions[0]? | throw "empty program"
  let regs : Reg64s := {
    rdi := .ofNat tableAddr, rsi := (if keypairCase then 2 else 1), rdx := .ofNat e.index,
    rcx := .ofNat outputAddr, rsp := .ofNat stackAddr,
    rbx := 0x11, rbp := 0x22, r12 := 0x33, r13 := 0x44, r14 := 0x55, r15 := 0x66}
  let initial : MachineState := ⟨{regs, dmem := memory}, .ofNat entry.pc⟩
  let r1 ← runMachine input initial 0
  let r2 ← runMachine input ⟨{r1.state.data with regs}, .ofNat entry.pc⟩ 0
  for r in [r1, r2] do
    unless r.state.data.regs.rax == 0 && r.state.data.regs.rsp.toNat == stackAddr + 8 do
      throw "counterexample did not return NULL into its entry frame"
    unless (← readNat r.state outputAddr 8) == 0xfeedface do throw "output changed on miss"
  let peerField := (← entryAddr e input.offsets) + input.offsets.peer
  unless (← readNat initial peerField 8) == peerAddress &&
      (← readNat r1.state peerField 8) == 0 && (← readNat r2.state peerField 8) == 0 do
    throw "expected kernel to clear the index entry peer pointer"
  -- The helper's TEST/JZ is at 0xffffffff81399822/25. Its two
  -- successors identify null/non-null without using the mirror's answer.
  let nullBranch := 0xffffffff81399825
  let outcome (r : Run) : Except String Bool := do
    let some i := r.pcs.toList.idxOf? nullBranch | throw "helper null check missing"
    let some successor := r.pcs[i+1]? | throw "helper successor missing"
    if successor == 0xffffffff813998ed then return true
    if successor == 0xffffffff8139982b then return false
    throw "unexpected helper null-check successor"
  let firstNull ← outcome r1
  let secondNull ← outcome r2
  unless !firstNull && secondNull do throw "expected changed null-peer decision on repeated lookup"
  let labels1 := after1.steps.map Leanux.Step.label
  let labels2 := after2.steps.map Leanux.Step.label
  for (r, source) in [(r1, after1), (r2, after2)] do
    let points ← Binary.LookupObservation.observe w.netRxSection r.history.toList
    unless (points.filterMap (·.step)).toArray == source.steps do
      throw "two-lookup regression decision sequence mismatch"
  let alias ← if keypairCase then do
      let some d := after2.wg.dev | throw "device disappeared"
      let some k := d.keypairs.get? 0 | throw "keypair disappeared"
      unless k.peer.isNone do throw "keypair owner word was not cleared"
      pure (Json.mkObj [("physical_entry_peer", toJson (0 : Nat)),
        ("mirror_keypair_peer", toJson k.peer), ("mirror_peer_address", toJson peerAddress)])
    else pure Json.null
  return Json.mkObj [
    ("status", toJson "fixed two-lookup regression passed"),
    ("scope", toJson "synthetic accepted mirror state; kernel reachability not established"),
    ("machine_null_peer_decisions", toJson [firstNull, secondNull]),
    ("mirror_first", toJson labels1), ("mirror_second", toJson labels2),
    ("machine_instructions", toJson [r1.pcs.size, r2.pcs.size]),
    ("machine_peer_pointer_before", toJson peerAddress),
    ("machine_peer_pointer_after", toJson (0 : Nat)),
    ("mirror_peer_id_after", toJson (none : Option Nat)), ("keypair_alias", alias)]

/-! Concrete tests of the named service specifications against the pinned
    fetched instruction bodies. These tests are not used by any proof. -/
namespace ServiceTests
open Binary Binary.TrustBase
local instance : Labels := Image.linkedLabels

def run (initial : MachineState) (seed : UInt64) : Except String (MachineState × Nat) := do
  let mut r : Run := {state := initial}
  for n in [:1000] do
    if r.state.pc == Int64.ofNat stopAddr then return (r.state, n)
    let some decoded := pinnedFetch r.state.pc
      | throw s!"missing pinned instruction {r.state.pc.toBitVec.toNat}"
    r ← interpret seed r decoded.instruction r.state.pc.toBitVec.toNat decoded.size
  throw "service instruction budget exhausted"

def fixture (mode count capacity preempt : Nat) : MachineState := Id.run do
  let mut memory : DataMem := {}
  memory := materializeServices memory
  memory := put memory 0xffffffff81cc85c8 4 preempt
  memory := put memory (0x800000 + 0x6e0) 4 mode
  memory := put memory (0x800000 + 0x6e4) 4 capacity
  memory := put memory coverageAddr 8 count
  memory := put memory stackAddr 8 stopAddr
  return {pc := 0, data := {dmem := memory, regs := {
    rsp := .ofNat stackAddr, rdi := 0xfedcba9876543210, rsi := 0x123456789abcdef0,
    rbx := 11, rbp := 12, r12 := 13, r13 := 14, r14 := 15, r15 := 16}}}

def checkABI (before after : MachineState) : Except String Unit := do
  unless after.pc == Int64.ofNat stopAddr && after.data.regs.rsp == before.data.regs.rsp + 8 &&
      after.data.regs.rbx == before.data.regs.rbx && after.data.regs.rbp == before.data.regs.rbp &&
      after.data.regs.r12 == before.data.regs.r12 && after.data.regs.r13 == before.data.regs.r13 &&
      after.data.regs.r14 == before.data.regs.r14 && after.data.regs.r15 == before.data.regs.r15 do
    throw "service return/frame mismatch"

-- Compare every mapped byte, and reject any newly mapped byte too.
def checkMemory (expected actual : DataMem) : Except String Unit := do
  unless expected == actual do throw "service memory mismatch"

def callback (kind : KcovKind) (pc : Nat) (mode count capacity preempt : Nat) : Except String Nat := do
  let before := {fixture mode count capacity preempt with pc := .ofNat pc}
  let some stores := KcovPlan kind before | throw "test fixture is not KCOV-ready"
  let expected := stores.foldl (fun m w => m.storeInt w.address 8 w.value.toInt) before.data.dmem
  let mut total := 0
  for seed in [0, 0xffffffffffffffff] do
    let (after, n) ← run before seed
    checkABI before after
    checkMemory expected after.data.dmem
    total := total + n
  return total

def bh (count : Nat) : Except String Nat := do
  let initial := fixture 2 0 1024 count
  let before := {initial with pc := .ofNat 0xffffffff810732c0, data := {initial.data with regs := {initial.data.regs with rsi := 512}}}
  let expected := put before.data.dmem 0xffffffff81cc85c8 4 (count - 512)
  let mut total := 0
  for seed in [0, 0xffffffffffffffff] do
    let (after, n) ← run before seed
    checkABI before after
    checkMemory expected after.data.dmem
    total := total + n
  return total

def tests : Except String Nat := do
  let mut total := 0
  for (kind, address) in [(KcovKind.pc, 0xffffffff810f31f0),
      (.cmp4, 0xffffffff810f4080), (.constCmp4, 0xffffffff810f4100),
      (.constCmp1, 0xffffffff810f40c0)] do
    let mode := if kind == .pc then 2 else 3
    total := total + (← callback kind address mode 0 1024 0)
    total := total + (← callback kind address mode 1024 1024 0)
    total := total + (← callback kind address 0 0 1024 0)
    total := total + (← callback kind address mode 0 1024 0x10000)
  total := total + (← bh 512)
  total := total + (← bh 1024)
  return total

/-- Concrete null helper path with actual callback instructions. This is a
    test of the physical proof case, not a kernel entry snapshot or Pre witness. -/
def peerNull : Except String Nat := do
  let mut total := 0
  for (mode, capacity) in [(2, 1024), (3, 1024), (0, 1024), (2, 0)] do
    let base := fixture mode 0 capacity 0
    let memory := base.data.dmem.storeBytes (.ofNat 64 (stackAddr-64)) (List.replicate 64 0)
    let regs := {base.data.regs with rdi := 0, rbx := 0x8000000000000011, r15 := 0xfedcba9876543210}
    let before := {base with pc := Image.PeerGet.entry, data := {base.data with dmem := memory, regs}}
    let mut expected := memory
    for (value, n) in [before.data.regs.r15, before.data.regs.r14, before.data.regs.r13,
        before.data.regs.r12, before.data.regs.rbp, before.data.regs.rbx].zipIdx do
      expected := put expected (stackAddr-(n+1)*8) 8 value.toNat
    expected := put expected (stackAddr-56) 8 (Image.PeerGet.entry+0xa2).toBitVec.toNat
    if mode == 2 && capacity != 0 then
      expected := put expected coverageAddr 8 2
      expected := put expected (coverageAddr+8) 8 (Image.PeerGet.entry+0x12).toBitVec.toNat
      expected := put expected (coverageAddr+16) 8 (Image.PeerGet.entry+0xa2).toBitVec.toNat
    for seed in [0, 0xffffffffffffffff] do
      let (after, n) ← run before seed
      checkABI before after
      unless after.data.regs.rax == 0 do throw "null peer-get returned a non-null pointer"
      checkMemory expected after.data.dmem
      total := total + n
  return total
/-- Nonnull helper paths with actual decoded callback bodies. Expected
    coverage and comparison records are explicit path observations; expected
    peer memory is one unchanged or incremented word. No test proves Pre. -/
def peerNonnull : Except String Nat := do
  let mut total := 0
  for old in [0, 1, 0x7ffffffe] do
    for (mode, capacity) in [(2, 1024), (3, 1024), (0, 1024), (2, 0), (3, 0), (2, 3), (3, 6)] do
      let base := fixture mode 0 capacity 0
      let memory := base.data.dmem.storeBytes (.ofNat 64 (stackAddr-64)) (List.replicate 64 0)
      let memory := put memory (0x600000+0x420) 4 old
      let regs := {base.data.regs with rdi := 0x600000, rbx := 0x8000000000000011, r15 := 0xfedcba9876543210}
      let before := {base with pc := Image.PeerGet.entry, data := {base.data with dmem := memory, regs}}
      let mut expected := memory
      for (value, n) in [before.data.regs.r15, before.data.regs.r14, before.data.regs.r13,
          before.data.regs.r12, before.data.regs.rbp, before.data.regs.rbx].zipIdx do
        expected := put expected (stackAddr-(n+1)*8) 8 value.toNat
      expected := put expected (stackAddr-56) 8 (Image.PeerGet.entry+0xa2).toBitVec.toNat
      if old != 0 then expected := put expected (0x600000+0x420) 4 (old+1)
      let pcs : List Nat := if old == 0 then [0x12, 0x20, 0x32, 0xb5, 0xc3, 0xd4, 0xa2]
        else [0x12, 0x20, 0x32, 0x44, 0x6e, 0x80, 0x94, 0xa2]
      if mode == 2 then
        let mut count := 0
        for offset in pcs do
          if count+1 < capacity then
            count := count+1
            expected := put expected coverageAddr 8 count
            expected := put expected (coverageAddr+8*count) 8
              (Image.PeerGet.entry+Int64.ofNat offset).toBitVec.toNat
      let comparisons : List (Nat × Nat × Nat) := if old == 0 then
          [(5, 0, 0x3b), (5, 0, 0xbe), (5, 1, 0xcf), (5, 0, 0xdd)]
        else [(5, old, 0x3b), (1, 1, 0x60), (5, old, 0x77), (5, old+1, 0x8a), (5, old, 0x9d)]
      if mode == 3 then
        let mut count := 0
        for (tag, arg, offset) in comparisons do
          if 4*count+5 ≤ capacity then
            expected := put expected (coverageAddr+8*(4*count+1)) 8 tag
            expected := put expected (coverageAddr+8*(4*count+2)) 8 0
            expected := put expected (coverageAddr+8*(4*count+3)) 8 arg
            expected := put expected (coverageAddr+8*(4*count+4)) 8
              (Image.PeerGet.entry+Int64.ofNat offset).toBitVec.toNat
            count := count+1
            expected := put expected coverageAddr 8 count
      for seed in [0, 0xffffffffffffffff] do
        let (after, n) ← run before seed
        checkABI before after
        unless after.data.regs.rax == (if old == 0 then 0 else 0x600000) do
          throw s!"nonnull peer-get result mismatch: count={old}, mode={mode}, capacity={capacity}"
        checkMemory expected after.data.dmem
        total := total+n
  return total
end ServiceTests

namespace AllowedipsProbe
open Leanux Leanux.WG

/-- All outcomes come from executed edges/registers; no expected source
    decisions are inputs. Peer-get's already-tested observer is reused. -/
def edge (input : Input) (s t : MachineState) : Except String (List Step) := do
  let l := Int64.ofNat input.entry
  let c := Int64.ofNat input.commonEntry
  let decision (d : Decision) (b : Bool) : Step := {decision := d, outcome := b}
  let choose := Binary.LookupObservation.choice
  if s.pc == l+0x41 then
    return [decision .swapEndian32 (← choose t.pc (l+0x171) (l+0x47))]
  if s.pc == l+0x5b then
    return [decision .swapEndian128 (← choose t.pc (l+0x14f) (l+0x61))]
  if s.pc == l+0x81 then
    let more ← choose t.pc (l+0x87) (l+0x184)
    return [decision .findNodeNode more] ++ if more then [] else [decision .lookupFound false]
  if s.pc == l+0xd3 then
    return [decision .findNodeNode (← choose t.pc (l+0xd5) (l+0x101))]
  if s.pc == c+0x24 then
    return [decision .commonBits32 (← choose t.pc (c+0x4c) (c+0x26))]
  if s.pc == c+0x3c then
    return [decision .commonBits128 (← choose t.pc (c+0x75) (c+0x3e))]
  if s.pc == c+0x91 then
    return [decision .fls128High (← choose t.pc (c+0x93) (c+0xc4))]
  if s.pc == l+0xff then
    return [decision .findNodePrefixMatches (← choose t.pc (l+0x90) (l+0x101))]
  if s.pc == l+0x9b then
    unless t.pc == l+0x9f do throw "unexpected CMOV successor"
    return [decision .findNodeHasPeer (s.data.regs.rax != 0)]
  if s.pc == l+0xb2 then
    return [decision .findNodeFullLength (← choose t.pc (l+0x101) (l+0xb4))]
  if s.pc == l+0x109 then
    return [decision .lookupFound (← choose t.pc (l+0x10b) (l+0x184))]
  if s.pc == l+0x11c then
    return [decision .lookupPeerGone (← choose t.pc (l+0x74) (l+0x122))]
  return (← Binary.LookupObservation.edge 0 s t).filterMap (·.step)

def probe (input : Input) : Except String Json := do
  unless input.budget > 0 && input.budget ≤ 100000 do throw "invalid explicit instruction budget"
  unless input.entryPreempt == 512 do throw "allowedips transmit fixture expects nested BH disable"
  let trace ← Leanux.Runner.parseTrace input.trace
  unless trace.id == "b1_trie_routing" && (input.operation == 5 || input.operation == 8) do
    throw "allowedips probe expects b1_trie_routing operation 5 or 8"
  let some (.wgXmit family key _ _) := trace.ops[input.operation]? | throw "operation is not wg_xmit"
  let priorWorld ← replayRecordedPrefix input.trace input.operation
  -- The selected unicast operation's pre-lookup code changes no trie or
  -- peer counts. syscall resets its decision/NET_RX context before that code.
  let w := {priorWorld with ambient := {priorWorld.ambient with steps := #[], hidden := some [], netRxSection := 0, netRxSections := 0}}
  let some dev := w.wg.dev | throw "no device after recorded prefix"
  let width := if family == 4 then 32 else 128
  let root := if family == 4 then dev.peerAllowedips.root4 else dev.peerAllowedips.root6
  let (answer, after) ← (Binary.Source.lookup root width key).run w |>.mapError Stop.message
  let some afterDev := after.wg.dev | throw "lookup lost device"
  let memory ← materialize dev input.offsets key width input.preempt input.entryPreempt
  let regs : Reg64s := {
    rdi := .ofNat (nodePointer root), rsi := .ofNat width,
    rdx := .ofNat keyAddr, rsp := .ofNat stackAddr,
    rbx := 0x11, rbp := 0x22, r12 := 0x33, r13 := 0x44, r14 := 0x55, r15 := 0x66}
  let initial : MachineState := ⟨{regs, dmem := memory}, .ofNat input.entry⟩
  let execute := runProgram input.instructions input.labels input.hooks input.preempt initial
  let r ← execute 0 true input.budget input.entryPreempt
  let alternate ← execute 0xffffffffffffffff true input.budget input.entryPreempt
  unless r.coverage == alternate.coverage && r.comparisons == alternate.comparisons &&
      r.pcs == alternate.pcs && r.state.data.regs == alternate.state.data.regs &&
      r.state.data.dmem == alternate.state.data.dmem do throw "undefined seeds change observable execution"
  unless r.state.data.regs.rax.toNat == nullablePeerAddr answer &&
      r.state.data.regs.rsp.toNat == stackAddr+8 do throw "allowedips return/stack mismatch"
  for reg in [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15] do
    unless r.state.data.regs.get64 reg == initial.data.regs.get64 reg do throw "allowedips callee-save mismatch"
  let expected ← materialize afterDev input.offsets key width input.preempt input.entryPreempt
  let stackBase := BitVec.ofNat 64 (stackAddr-0x800)
  let some stackBytes := memory.loadBytes stackBase 0x810 | throw "initial stack missing"
  unless (← readNat r.state coverageAddr 8) == r.coverage.size do throw "KCOV count mismatch"
  for i in [:r.coverage.size] do
    unless (← readNat r.state (coverageAddr+8*(i+1)) 8) == r.coverage[i]! do throw "KCOV record mismatch"
  let finalMemory := (r.state.data.dmem.storeBytes stackBase stackBytes).storeBytes
    (.ofNat 64 coverageAddr) (List.replicate coverageBytes 0)
  unless finalMemory == expected do throw "allowedips non-stack memory differs from source result"
  let steps ← Binary.observeHistory (edge input) r.history.toList
  unless steps.toArray == after.steps do
    throw s!"allowedips decision mismatch: machine={steps.map Step.label}, source={after.steps.map Step.label}"
  let nodes := dev.nodes.toList.map fun (id, n) => Json.mkObj [
    ("id", toJson id), ("peer", toJson n.peer), ("cidr", toJson n.cidr),
    ("bitlen", toJson n.bitlen), ("bits", toJson n.bits), ("children", toJson n.bit)]
  return Json.mkObj [("status", toJson "pass"), ("operation", toJson input.operation),
    ("family", toJson family), ("key", toJson key), ("root", toJson root), ("nodes", toJson nodes),
    ("peer_counts", toJson (dev.peers.toList.map fun (id, p) => (id, p.refcount))),
    ("result", toJson answer), ("instructions_executed", toJson r.pcs.size),
    ("instruction_budget", toJson input.budget), ("fixture_entry_preempt", toJson input.entryPreempt),
    ("coverage", toJson r.coverage), ("comparisons", toJson r.comparisons),
    ("decisions", toJson (steps.map Step.label)), ("mirror_decisions", toJson (after.steps.map Step.label)),
    ("services", toJson "decoded bodies, KCOV_TRACE_PC"),
    ("undefined_choices", toJson r.undefinedCount), ("write_accesses", toJson r.writes),
    ("memory", toJson "all materialized non-stack bytes match the source lookup result")]
end AllowedipsProbe

def main (args : List String) : IO UInt32 := do
  if let ["allowedips", path] := args then
    let input ← liftE (Json.parse (← IO.FS.readFile path) >>= fromJson?)
    let result ← liftE (AllowedipsProbe.probe input)
    IO.println result.compress
    return 0
  if args == ["peer-nonnull"] then
    match ServiceTests.peerNonnull with
    | .error message => IO.eprintln message; return 1
    | .ok n => IO.println s!"PASS: 21 nonnull peer-get cases, two undefined-value seeds, {n} instructions"; return 0
  if args == ["peer-null"] then
    match ServiceTests.peerNull with
    | .error message => IO.eprintln message; return 1
    | .ok n => IO.println s!"PASS: 4 null peer-get cases, two undefined-value seeds, {n} instructions"; return 0
  if args == ["service-tests"] then
    match ServiceTests.tests with
    | .error message => IO.eprintln message; return 1
    | .ok n => IO.println s!"PASS: 18 service cases, two undefined-value seeds, {n} instructions"; return 0
  if let ["actual-services", path] := args then
    let input ← liftE (Json.parse (← IO.FS.readFile path) >>= fromJson?)
    let result ← liftE (probe input true)
    IO.println result.compress
    return 0
  if let ["dead-peer", path] := args then
    let input ← liftE (Json.parse (← IO.FS.readFile path) >>= fromJson?)
    let result ← liftE (deadPeerCounterexample input)
    IO.println result.compress
    return 0
  if let ["dead-keypair", path] := args then
    let input ← liftE (Json.parse (← IO.FS.readFile path) >>= fromJson?)
    let result ← liftE (deadPeerCounterexample input true)
    IO.println result.compress
    return 0
  if let ["run", path] := args then
    let input ← liftE (Json.parse (← IO.FS.readFile path) >>= fromJson?)
    let result ← liftE (probe input)
    IO.println result.compress
    return 0
  if let ["parse", path] := args then
    let lines := (← IO.FS.readFile path).splitOn "\n"
    for line in lines do
      if line.isEmpty then continue
      match Kraken.X64.Parser.parse line with
      | .ok _ => IO.println (Json.mkObj [("asm", toJson line), ("ok", toJson true)]).compress
      | .error e => IO.println (Json.mkObj [("asm", toJson line), ("ok", toJson false), ("error", toJson e)]).compress
    return 0
  IO.eprintln "usage: binary-probe parse FILE"
  return 1
