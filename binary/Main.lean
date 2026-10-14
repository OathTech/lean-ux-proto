import Kraken.X64.Parser
import Kraken.X64.Semantics
import Leanux.Runner

open Lean

structure Instruction where
  pc : Nat
  size : Nat
  asm : String
  deriving FromJson

structure Offsets where
  tableSize : Nat
  buckets : Nat
  headSize : Nat
  first : Nat
  entrySize : Nat
  peer : Nat
  hash : Nat
  next : Nat
  pprev : Nat
  kind : Nat
  index : Nat
  deriving FromJson

structure ProbeInput where
  instructions : Array Instruction
  labels : Array (String × Nat)
  hooks : Array (Nat × String)
  offsets : Offsets
  preempt : Nat
  trace : Json
  operation : Nat
  query : Nat
  deriving FromJson

def liftE {α} (x : Except String α) : IO α :=
  match x with | .ok a => pure a | .error e => throw (IO.userError e)

/-- Replay the recorded prefix with the same entry settings as executeTrace.
    This probe deliberately accepts one corpus case, not arbitrary traces. -/
def replayPrefix (j : Json) (count : Nat) : Except String Leanux.World := do
  let t ← Leanux.Runner.parseTrace j
  unless count == 3 && t.ops.size > count && t.hidden.isSome do
    throw "probe requires the recorded three-operation prefix"
  unless t.seccompPrefill == 0 do throw "probe does not support a seccomp prefill"
  let mut w : Leanux.World := {
    k := Leanux.Runner.initialKernel t.rlimit t.net t.bare t.foreign t.stepped t.seccompChild
    env := Leanux.Runner.harnessEnv, timing := Leanux.Env.timing
    portBound := Leanux.Env.portBound, fixtureNetDevices := Leanux.Env.fixtureNetDevices
    foreignCreator := t.foreign, netnsCHolders := if t.foreign then [9, 8, 5, 4] else []
    allocArmed := t.allocArmed, routes := t.routes, armRecords := t.armRecords
    dstCacheRecords := t.dstCacheRecords, napiBeforePut := t.napiBeforePut }
  let mut results := #[]
  let mut ends := #[]
  for i in [:count] do
    w := {w with hidden := t.hidden.map (·[i]!), netRxRaised := false}
    let some op := t.ops[i]? | throw "prefix operation missing"
    let (ret, next) ← (Leanux.syscall (Leanux.Runner.toSyscall results ends i op)).run w
      |>.mapError Leanux.Stop.message
    let (_, next) ← Leanux.skipAmbient.run next |>.mapError Leanux.Stop.message
    unless next.hidden == some [] do throw s!"unconsumed prefix records at {i}"
    unless next.suspended.isEmpty && !next.netRxRaised do throw "incomplete prefix dispatch"
    w := next
    results := results.push ret
    ends := ends.push (if ret == 0 then w.userFds else none)
  return {w with steps := #[], hidden := some []}

def tableAddr : Nat := 0x100000
def entryAddr (i : Nat) : Nat := 0x200000 + i * 0x100
def outputAddr : Nat := 0x300000
def stackAddr : Nat := 0x400800
def stopAddr : Nat := 0x500000

def put (m : DataMem) (a size v : Nat) : DataMem :=
  m.storeInt (.ofNat 64 a) size v

/-- Heap materialization is generated from the mirror list and DWARF offsets.
    Synthetic addresses are related to identities, not claimed to be kernel pointers. -/
def materialize (entries : List Leanux.WG.IndexEntry) (o : Offsets) (preempt : Nat) : DataMem := Id.run do
  let mut m : DataMem := (List.replicate o.tableSize (0 : UInt8)).At (.ofNat 64 tableAddr)
  m := m.storeBytes (.ofNat 64 (stackAddr - 0x800)) (List.replicate 0x810 0)
  m := put m stackAddr 8 stopAddr
  m := put m outputAddr 8 0xfeedface
  m := put m preempt 4 0
  for (e, i) in entries.zipIdx do
    let addr := entryAddr i
    m := m.storeBytes (.ofNat 64 addr) (List.replicate o.entrySize 0)
    let bucket := e.index % 8192
    let bucketAddr := tableAddr + o.buckets + bucket * o.headSize + o.first
    let before := (entries.take i).zipIdx.filter (fun (e, _) => e.index % 8192 == bucket)
    let after := (entries.zipIdx.drop (i+1)).find? (fun (e, _) => e.index % 8192 == bucket)
    let prevAddr := match before.getLast? with
      | none => bucketAddr
      | some (_, j) => entryAddr j + o.hash + o.next
    if before.isEmpty then m := put m bucketAddr 8 (addr + o.hash)
    m := put m (addr + o.peer) 8 (0x600000 + e.peer * 0x1000)
    m := put m (addr + o.hash + o.next) 8 (after.map (fun (_, j) => entryAddr j + o.hash) |>.getD 0)
    m := put m (addr + o.hash + o.pprev) 8 prevAddr
    m := put m (addr + o.kind) 4 (if e.kind == .handshake then 1 else 2)
    m := put m (addr + o.index) 4 e.index
  return m

structure Run where
  state : MachineState
  pcs : Array Nat := #[]
  coverage : Array Nat := #[]
  comparisons : Array (Nat × Nat × Nat) := #[]
  writes : Array (Nat × Nat) := #[]
  undefinedCount : Nat := 0

/-- Same deterministic undefined-value choice mechanism as Kraken's evaluator.
    Two seeds are run below; this is testing, not universal quantification. -/
partial def effects (seed : UInt64) (r : Run) : Effects → Except String Run
  | .done s => pure {r with state := s}
  | .require_read_access a w k => do
    unless (r.state.data.dmem.loadBytes a w.bytes).isSome do throw s!"unmapped read {a}"
    effects seed r (k ())
  | .require_write_access a w k => do
    unless (r.state.data.dmem.loadBytes a w.bytes).isSome do throw s!"unmapped write {a}"
    effects seed {r with writes := r.writes.push (a.toNat, w.bytes)} (k ())
  | .require_exec_access _ k => effects seed r (k ())
  | @Effects.undefined _ t k =>
    effects seed {r with undefinedCount := r.undefinedCount + 1} (k (t.from_hash seed))
  | .unimplemented e => throw e
  | .gp_unaligned a _ => throw s!"unaligned access {a}"
  | .nonmem_load _ a _ _ => throw s!"nonmemory load {a}"
  | .nonmem_store _ a _ _ => throw s!"nonmemory store {a}"

def readNat (s : MachineState) (a n : Nat) : Except String Nat := do
  let some bytes := s.data.dmem.loadBytes (.ofNat 64 a) n | throw s!"unmapped read at {a}"
  return (bytes.zipIdx.map fun (b, i) => b.toNat * 256^i).sum

def interpret [Labels] (seed : UInt64) (r : Run) (i : Instr) (pc size : Nat) : Except String Run :=
  effects seed r (i.interp r.state.data ⟨.ofNat pc, .ofNat (pc+size)⟩
    (fun d => .done ⟨d, .ofNat (pc+size)⟩) (fun p d => .done ⟨d, p⟩))

def runMachine (input : ProbeInput) (initial : MachineState) (seed : UInt64) : Except String Run := do
  let parsed ← input.instructions.mapM fun i => do
    let [.instr op] ← Kraken.X64.Parser.parse i.asm | throw s!"not one instruction: {i.asm}"
    return (i, op)
  let _ : Labels := ⟨fun l => .ofNat ((input.labels.find? (·.1 == l)).map (·.2) |>.getD 0)⟩
  let mut r : Run := {state := initial}
  for _ in [:1000] do
    let pc := r.state.pc.toBitVec.toNat
    if pc == stopAddr then return r
    if let some (_, name) := input.hooks.find? (·.1 == pc) then
      let ra ← readNat r.state r.state.data.regs.rsp.toNat 8
      if name == "__sanitizer_cov_trace_pc" then
        r := {r with coverage := r.coverage.push ra}
      else if name == "__sanitizer_cov_trace_cmp4" || name == "__sanitizer_cov_trace_const_cmp4" then
        let comparison := (ra, r.state.data.regs.rdi.toNat % (2^32), r.state.data.regs.rsi.toNat % (2^32))
        r := {r with comparisons := r.comparisons.push comparison}
      else if name == "__local_bh_enable_ip" then
        unless r.state.data.regs.rsi == 512 && (← readNat r.state input.preempt 4) == 512 do
          throw "environment summary requires one balanced BH-disable and no pending work"
        r := {r with state := {r.state with data := {r.state.data with
          dmem := put r.state.data.dmem input.preempt 4 0}}}
      else
        throw s!"unclassified or unreached-path call: {name}"
      r ← interpret seed r (.regular .W64 .W64 .ret) pc 1
    else
      let some (i, op) := parsed.find? (·.1.pc == pc) | throw s!"PC outside function: {pc}"
      r := {r with pcs := r.pcs.push pc}
      r ← interpret seed r op pc i.size
  throw "instruction budget exhausted"

def probe (input : ProbeInput) : Except String Json := do
  let w ← replayPrefix input.trace input.operation
  let some dev := w.k.wg | throw "no device after prefix"
  unless dev.indexTable.length == 1 do throw "expected one entry after recorded prefix"
  let before := dev.indexTable
  let (answer, after) ← (Leanux.WG.indexLookup [.handshake] input.query).run w
    |>.mapError Leanux.Stop.message
  unless answer.isNone && after.k == w.k do throw "expected read-only miss in the mirror"
  let memory := materialize before input.offsets input.preempt
  let some entry := input.instructions[0]? | throw "empty instruction list"
  let regs : Reg64s := {
    rdi := .ofNat tableAddr
    rsi := 1
    rdx := .ofNat input.query
    rcx := .ofNat outputAddr
    rsp := .ofNat stackAddr
    rbx := 0x11, rbp := 0x22, r12 := 0x33, r13 := 0x44, r14 := 0x55, r15 := 0x66 }
  let initial : MachineState := ⟨{regs, dmem := memory}, .ofNat entry.pc⟩
  let r ← runMachine input initial 0
  let alternate ← runMachine input initial 0xffffffffffffffff
  unless r.coverage == alternate.coverage && r.pcs == alternate.pcs && r.state.data.regs == alternate.state.data.regs &&
      r.state.data.dmem == alternate.state.data.dmem do throw "undefined-value seed changes observables"
  unless r.state.data.regs.rax == 0 && r.state.data.regs.rsp.toNat == stackAddr + 8 do
    throw "return or stack mismatch"
  for reg in [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15] do
    unless r.state.data.regs.get64 reg == initial.data.regs.get64 reg do throw s!"callee-save mismatch: {repr reg}"
  let stackBase := BitVec.ofNat 64 (stackAddr - 0x800)
  let some stackBytes := memory.loadBytes stackBase 0x810 | throw "initial stack missing"
  unless r.state.data.dmem.storeBytes stackBase stackBytes == memory do
    throw "non-stack memory changed"
  -- A build-bound certificate for this one path. Events refer to instruction
  -- offsets; their outcomes come from the successor selected by Kraken.
  let mut decisions : Array String := #[]
  for i in [:r.pcs.size] do
    let pc := r.pcs[i]!
    let next := r.pcs[i+1]?.getD stopAddr
    if pc == entry.pc + 0x32 then
      decisions := decisions.push s!"wg_index_hashtable_lookup.entry={if next == entry.pc + 0x34 then 1 else 0}"
    if pc == entry.pc + 0x5c then
      decisions := decisions.push s!"wg_index_hashtable_lookup.index_matches={if next == entry.pc + 0x95 then 1 else 0}"
    if pc == entry.pc + 0x6a then
      decisions := decisions.push s!"wg_index_hashtable_lookup.entry={if next == entry.pc + 0x34 then 1 else 0}"
    if pc == entry.pc + 0x71 then
      decisions := decisions.push "wg_index_hashtable_lookup.found=0"
  let mirrorDecisions := after.steps.map Leanux.Step.label
  unless decisions == mirrorDecisions do throw s!"decision disagreement: machine={decisions}, mirror={mirrorDecisions}"
  return Json.mkObj [
    ("status", toJson "pass"), ("result", toJson "none/null"),
    ("instructions_executed", toJson r.pcs.size), ("coverage", toJson r.coverage),
    ("comparisons", toJson r.comparisons), ("decisions", toJson decisions),
    ("mirror_decisions", toJson mirrorDecisions), ("memory", toJson "all non-stack bytes unchanged"),
    ("entries", toJson (before.map fun e => e.index)), ("query", toJson input.query),
    ("undefined_choices", toJson r.undefinedCount), ("write_accesses", toJson r.writes)]

def main (args : List String) : IO UInt32 := do
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
