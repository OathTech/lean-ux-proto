import PairMemory
import MirrorLoop

namespace Binary.Pair
open Lean Leanux Leanux.WG

def makeNames (d : Device) (o : Offsets) : Except String Names := do
  let owners := (d.peers.toList.map fun (id, _) => IndexOwner.handshake id) ++
    (d.keypairs.toList.map fun (id, _) => IndexOwner.keypair id)
  return {
    table := tableAddr
    peers := d.peers.toList.map fun (id, _) => (id, peerAddr id)
    owners := ← owners.mapM fun owner => do return (owner, ← entryAddr ⟨0, owner⟩ o)}

def kindMask (kinds : List IndexKind) : Nat :=
  (if kinds.contains .handshake then 1 else 0) + (if kinds.contains .keypair then 2 else 0)

/-- These points belong to the pinned image, not the mirror's decision trace. -/
def header : Nat := Image.Lookup.entry.toBitVec.toNat + 0x42
def helper : Nat := Image.Lookup.entry.toBitVec.toNat + 0xb2
def tail : Nat := Image.Lookup.entry.toBitVec.toNat + 0x73

structure Session where
  names : Names
  world : World
  binary : Run
  call : Nat := 0

/-- Fixture construction happens once, before the first assertion. Subsequent
calls retain this heap and interpretation, including legitimate peer aliases. -/
def startSession (input : ProbeInput) (w : World) : Except String Session := do
  let some d := w.k.wg | throw "fixture has no device"
  let names ← makeNames d input.offsets
  let memory ← materializePeers d input.offsets (← materialize d input.offsets input.preempt)
  let memory := materializeServices memory
  assertMemory names input.offsets memory w
  return {names, world := w, binary := {state := ⟨{dmem := memory}, .ofNat stopAddr⟩}}

def addressOf (n : Names) (owner : IndexOwner) : Except String Nat := do
  let some (_, a) := n.owners.find? (·.1 == owner) | throw "unmapped source owner"
  return a

def advance (input : ProbeInput) (seed : UInt64) (r : Run) (stops : Array Nat) : Except String Run :=
  runUntil input.instructions input.labels input.hooks input.preempt r.state seed true 100000 0 stops (some r)

def assertHeader (input : ProbeInput) (s : Session) (query : Nat) (kinds : List IndexKind)
    (remaining : List IndexEntry) : Except String Unit := do
  assertMemory s.names input.offsets s.binary.state.data.dmem s.world
  let e :: _ := remaining | throw "binary at loop header after source exhausted its bucket"
  let a ← addressOf s.names e.owner
  let regs := s.binary.state.data.regs
  unless regs.rbx.toNat == a do
    throw s!"loop.cursor: binary={regs.rbx.toNat}, source owner={repr e.owner} at {a}"
  unless regs.r12.toNat == query && regs.r13.toNat == outputAddr && regs.r14.toNat == kindMask kinds do
    throw "loop.saved-locals: query, output pointer or kind mask differs"
  unless regs.rsp.toNat == stackAddr - 40 do throw "loop.stack-frame: wrong depth"
  unless (← readNat s.binary.state input.preempt 4) == 512 do throw "loop.preempt: expected disabled BH"
  let link := a + input.offsets.hash
  let previous ← (word s.binary.state.data.dmem "loop.pprev" (link + input.offsets.pprev) 8)
    |>.mapError DecodeError.message
  let actual ← (bucket s.names input.offsets s.binary.state.data.dmem (query % 8192)
    (s.names.owners.length + 1) link previous []).mapError DecodeError.message
  unless actual == remaining do throw s!"loop.remaining: binary={repr actual}, mirror={repr remaining}"

def within (a bytes base size : Nat) : Bool := base ≤ a && a + bytes ≤ base + size

/-- Actual write requests, including mapped-but-out-of-footprint writes. This
is a concrete check, not an execution-wide permissions or lifetime theorem. -/
def assertFootprint (input : ProbeInput) (n : Names) (r : Run) : Except String Unit := do
  for (a, bytes) in r.writes do
    unless within a bytes (stackAddr - 0x800) 0x800 || within a bytes coverageAddr coverageBytes ||
        within a bytes input.preempt 4 || within a bytes outputAddr 8 ||
        n.owners.any (fun (_, p) => within a bytes (p + input.offsets.peer) 8) ||
        n.peers.any (fun (_, p) => within a bytes (p + input.offsets.peerRefcount) 4) do
      throw s!"write footprint: {bytes} bytes at {a}"
  for (a, bytes) in r.reads do
    unless within a bytes (stackAddr - 0x800) 0x810 || within a bytes coverageAddr coverageBytes ||
        within a bytes input.preempt 4 || within a bytes outputAddr 8 ||
        within a bytes n.table input.offsets.tableSize ||
        n.owners.any (fun (_, p) => within a bytes p input.offsets.entrySize) ||
        n.peers.any (fun (_, p) => within a bytes (p + input.offsets.peerRefcount) 4) ||
        within a bytes 0xffffffff81cc85c0 8 || within a bytes 0xffffffff81cc85e0 2 ||
        within a bytes (0x800000 + 0x6e0) 4 || within a bytes (0x800000 + 0x6e4) 4 ||
        within a bytes (0x800000 + 0x6e8) 8 || within a bytes (0x800000 + 0x704) 4 do
      throw s!"read footprint: {bytes} bytes at {a}"

def assertReturn (input : ProbeInput) (n : Names) (initial : MachineState)
    (r : Run) (answer : Option (IndexOwner × PeerId)) : Except String Unit := do
  let expected ← match answer with
    | none => pure 0
    | some (owner, _) => addressOf n owner
  unless r.state.pc.toBitVec.toNat == stopAddr && r.state.data.regs.rax.toNat == expected &&
      r.state.data.regs.rsp.toNat == stackAddr + 8 do throw "return: PC, result or stack differs"
  for reg in [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15] do
    unless r.state.data.regs.get64 reg == initial.data.regs.get64 reg do throw s!"return: saved {repr reg}"
  let output ← match answer with
    | none => readNat initial outputAddr 8
    | some (_, id) => do
      let some (_, a) := n.peers.find? (·.1 == id) | throw "return: unmapped source peer"
      pure a
  unless (← readNat r.state outputAddr 8) == output do throw "return: output peer word differs"
  unless (← readNat r.state input.preempt 4) == 0 do throw "return: preempt count not restored"
  unless (← readNat r.state 0xffffffff81cc85e0 2) == 0 do throw "return: pending softirq changed"
  unless (← readNat r.state coverageAddr 8) == r.coverage.size do throw "return: KCOV count differs"
  for i in [:r.coverage.size] do
    unless (← readNat r.state (coverageAddr + 8*(i+1)) 8) == r.coverage[i]! do
      throw s!"return: KCOV record {i} differs"
  assertFootprint input n r

/-- Pause the actual mirror through its already-proved loop presentation.
Each side chooses its own successor. Headers are checked after at least one
binary instruction, and occurrences include an explicit call/iteration index. -/
def lookup (input : ProbeInput) (seed : UInt64) (s : Session) (query : Nat)
    (kinds : List IndexKind) : Except String (Session × Json) := do
  unless query < 2^32 do throw "query is outside its ABI width"
  assertMemory s.names input.offsets s.binary.state.data.dmem s.world
  let regs : Reg64s := {
    rdi := .ofNat s.names.table, rsi := .ofNat (kindMask kinds),
    rdx := .ofNat query, rcx := .ofNat outputAddr, rsp := .ofNat stackAddr,
    rbx := 0x11, rbp := 0x22, r12 := 0x33, r13 := 0x44, r14 := 0x55, r15 := 0x66}
  let initial : MachineState := ⟨{s.binary.state.data with regs}, Image.Lookup.entry⟩
  let r : Run := {state := initial, history := #[initial], coverage := s.binary.coverage}
  let (entries, world) ← (indexBucket query).run s.world |>.mapError Stop.message
  let mut paired := {s with world, binary := ← advance input seed r #[header, helper, tail]}
  let mut remaining := entries
  let mut acc : LookupMirror.Acc := (none, false)
  let mut visits := 0
  for occurrence in [:entries.length + 1] do
    if paired.binary.state.pc.toBitVec.toNat != header then break
    let context := s!"call {s.call}, header {occurrence}"
    (assertHeader input paired query kinds remaining).mapError (fun e => s!"{context}: {e}")
    let e :: rest := remaining | throw s!"{context}: no source iteration"
    let (step, nextWorld) ← (LookupMirror.body kinds query e acc).run paired.world |>.mapError Stop.message
    let nextRemaining := match step with | .yield _ => rest | .done _ => []
    unless nextRemaining.length < remaining.length do throw s!"{context}: loop measure did not decrease"
    acc := match step with | .yield a => a | .done a => a
    remaining := nextRemaining
    visits := visits + 1
    paired := {paired with
      world := nextWorld
      binary := ← advance input seed paired.binary #[header, helper, tail]}
  let reached := paired.binary.state.pc.toBitVec.toNat
  unless remaining.isEmpty do throw "binary left the bucket while the source still has iterations"
  unless reached == (if acc.1.isSome then helper else tail) do
    throw s!"loop exit: independently reached binary PC {reached} disagrees with source {repr acc}"
  assertMemory paired.names input.offsets paired.binary.state.data.dmem paired.world
  let (answer, after) ← (LookupMirror.finish acc).run paired.world |>.mapError Stop.message
  let result ← advance input seed paired.binary #[]
  assertMemory paired.names input.offsets result.state.data.dmem after
  assertReturn input paired.names initial result answer
  -- An extra adapter regression, not the runtime relation: source presentation
  -- and the actual exported function have equal results, kernel states and logs.
  -- Full source equality is supplied by LookupMirror.indexLookup_eq.
  let (directAnswer, directAfter) ← (indexLookup kinds query).run s.world |>.mapError Stop.message
  unless answer == directAnswer && after.k == directAfter.k && after.steps == directAfter.steps do throw "source adapter differs from indexLookup"
  let report := Json.mkObj [("call", toJson s.call), ("query", toJson query),
    ("loop_headers", toJson visits), ("result", toJson (reprStr answer)),
    ("instructions", toJson result.pcs.size), ("writes_checked", toJson result.writes.size),
    ("reads_checked", toJson result.reads.size)]
  return ({paired with world := after, binary := result, call := s.call + 1}, report)

end Binary.Pair
