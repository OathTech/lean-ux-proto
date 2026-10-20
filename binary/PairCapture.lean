import SourceAdapter
import PairIndex

namespace Binary.Pair.Capture
open Lean Leanux Leanux.WG

structure Registers where
  rax : Nat
  rbx : Nat
  rcx : Nat
  rdx : Nat
  rsi : Nat
  rdi : Nat
  rsp : Nat
  rbp : Nat
  r8 : Nat
  r9 : Nat
  r10 : Nat
  r11 : Nat
  r12 : Nat
  r13 : Nat
  r14 : Nat
  r15 : Nat
  rip : Nat
  eflags : Nat
  deriving FromJson

def Registers.state (r : Registers) (m : DataMem) : Except String MachineState := do
  unless [r.rax, r.rbx, r.rcx, r.rdx, r.rsi, r.rdi, r.rsp, r.rbp, r.r8, r.r9,
      r.r10, r.r11, r.r12, r.r13, r.r14, r.r15, r.rip].all (· < 2^64) && r.eflags < 2^32 do
    throw "captured register exceeds its width"
  let regs : Reg64s := {
    rax := .ofNat r.rax, rbx := .ofNat r.rbx, rcx := .ofNat r.rcx, rdx := .ofNat r.rdx,
    rsi := .ofNat r.rsi, rdi := .ofNat r.rdi, rsp := .ofNat r.rsp, rbp := .ofNat r.rbp,
    r8 := .ofNat r.r8, r9 := .ofNat r.r9, r10 := .ofNat r.r10, r11 := .ofNat r.r11,
    r12 := .ofNat r.r12, r13 := .ofNat r.r13, r14 := .ofNat r.r14, r15 := .ofNat r.r15 }
  let status : StatusFlags := ⟨r.eflags.testBit 0, r.eflags.testBit 2, r.eflags.testBit 4,
    r.eflags.testBit 6, r.eflags.testBit 7, r.eflags.testBit 11⟩
  -- The captured anchor runs at CPL 0. Arithmetic flags remain in `status`;
  -- `pushFlags` masks those bits out of this separate system component.
  let system : SystemFlags := {bits := .ofNat 64 r.eflags,cpl := 0}
  return ⟨{regs, status, system, dmem := m}, .ofNat r.rip⟩

structure Block where
  address : Nat
  bytes : Array Nat
  deriving FromJson

/-- No relocation, zero filling, or expected source values enter the loader.
Overlapping capture blocks must agree byte for byte. -/
def loadMemory (blocks : Array Block) : Except String DataMem := do
  let mut memory : DataMem := {}
  for block in blocks do
    unless block.address > 0 && block.address + block.bytes.size ≤ 2^64 do
      throw "NULL or wrapping capture block"
    for i in [:block.bytes.size] do
      let value := block.bytes[i]!
      unless value < 256 do throw "captured byte exceeds eight bits"
      let address := BitVec.ofNat 64 (block.address + i)
      if let some old := memory.get? address then
        unless old.toNat == value do throw s!"overlapping capture bytes disagree at {address}"
      memory := memory.insert address value.toUInt8
  return memory

structure Endpoint where
  registers : Registers
  blocks : Array Block
  deriving FromJson

structure PeerRoot where
  address : Nat
  publicKey : Array Nat
  deriving FromJson

structure Entry extends Endpoint where
  peers : Array PeerRoot
  keypairs : Array Nat
  device : Nat
  task : Nat
  coverage : Nat
  capacity : Nat
  coverageUsed : Nat
  coverageCapturedWords : Nat
  deriving FromJson

structure Snapshot where
  trace : String
  operation : Nat
  instructionBudget : Nat
  executionMode : String
  executedPCs : Array Nat
  completedOperations : Array Nat
  initial : Entry
  returned : Endpoint
  deriving FromJson

def member (layout : Json) (object field : String) : Except String Nat := do
  let object ← layout.getObjVal? object
  let members ← object.getObjVal? "members"
  members.getObjValAs? Nat field

/-- Public keys identify peers across the two independent executions. This
pilot refuses keypair identity setup until its allocation interpretation exists;
it does not change reconstruction's target or exclude any dead-peer branch. -/
def names (input : ProbeInput) (snapshot : Snapshot) (layout : Json)
    (initial : MachineState) (d : Device) : Except String Names := do
  unless snapshot.initial.keypairs.isEmpty && d.keypairs.isEmpty do
    throw "captured pilot needs a keypair identity interpretation"
  let keyOffset := (← member layout "wg_peer" "handshake") +
    (← member layout "noise_handshake" "remote_static")
  let mut peers := []
  for (id, peer) in d.peers.toList do
    let candidates := snapshot.initial.peers.filter (fun p => p.publicKey.toList == peer.remoteStatic.map UInt8.toNat)
    unless candidates.size == 1 do throw s!"peer[{id}]: public key does not identify exactly one captured peer"
    let some p := candidates[0]? | throw "peer identity candidate missing"
    let some bytes := initial.data.dmem.loadBytes (.ofNat 64 (p.address + keyOffset)) 32
      | throw "peer identity key bytes are missing"
    unless bytes.map UInt8.toNat == p.publicKey.toList do throw "peer identity metadata differs from captured bytes"
    peers := peers ++ [(id, p.address)]
  unless peers.length == snapshot.initial.peers.size do throw "uninterpreted captured peers"
  let n : Names := {
    table := initial.data.regs.rdi.toNat
    peers := peers
    owners := peers.map fun (id, a) => (.handshake id, a + input.offsets.peerHandshake + input.offsets.handshakeEntry) }
  n.validate input.offsets |>.mapError DecodeError.message
  unless (← readNat initial (snapshot.initial.device + Binary.Layouts.device_index_hashtable) 8) == n.table do
    throw "captured device table pointer differs from ABI"
  return n

def callFrame (input : ProbeInput) (snapshot : Snapshot) (layout : Json)
    (initial : MachineState) : Except String CallFrame := do
  let pcpu := input.preempt - (← member layout "pcpu_hot" "preempt_count")
  let currentTask := pcpu + (← member layout "pcpu_hot" "current_task")
  let pending := pcpu + (← member layout "pcpu_hot" "softirq_pending")
  let e := snapshot.initial
  unless (← readNat initial currentTask 8) == e.task &&
      (← readNat initial (e.task + 0x6e0) 4) == 2 &&
      (← readNat initial (e.task + 0x6e4) 4) == e.capacity &&
      (← readNat initial (e.task + 0x6e8) 8) == e.coverage &&
      (← readNat initial e.coverage 8) == e.coverageUsed do
    throw "captured service metadata differs from memory"
  unless e.coverageUsed < e.coverageCapturedWords && e.coverageCapturedWords ≤ e.capacity do
    throw "invalid captured coverage extent"
  unless 0 < snapshot.instructionBudget && snapshot.instructionBudget ≤ 1000000 do
    throw "invalid captured execution budget"
  return {
    stack := initial.data.regs.rsp.toNat, output := initial.data.regs.rcx.toNat,
    returnPC := (← readNat initial initial.data.regs.rsp.toNat 8),
    entryPreempt := (← readNat initial input.preempt 4),
    coverage := e.coverage, coverageSize := e.coverageCapturedWords * 8,
    task := e.task, currentTask, pending, budget := snapshot.instructionBudget }

/-- Return comparison is an independent concrete test. Compare every captured
byte as well as all general registers and the status flags Kraken represents.
This deliberately starts stronger than the source observation relation: any
undefined/dead-scratch discrepancy must be diagnosed before relaxing the test. -/
def compareEndpoint (endpoint : Endpoint) (actual : MachineState) : Except String Nat := do
  let expected ← endpoint.registers.state (← loadMemory endpoint.blocks)
  unless actual.pc == expected.pc do throw "captured endpoint PC differs"
  for reg in [Reg64.rax, .rbx, .rcx, .rdx, .rsi, .rdi, .rsp, .rbp,
      .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] do
    unless actual.data.regs.get64 reg == expected.data.regs.get64 reg do
      throw s!"captured endpoint {repr reg}: Kraken={actual.data.regs.get64 reg}, kernel={expected.data.regs.get64 reg}"
  let mut checked := 0
  for block in endpoint.blocks do
    for i in [:block.bytes.size] do
      let address := BitVec.ofNat 64 (block.address + i)
      let some byte := actual.data.dmem.get? address | throw s!"captured endpoint byte missing at {address}"
      unless byte.toNat == block.bytes[i]! do
        throw s!"captured endpoint memory at {address}: Kraken={byte.toNat}, kernel={block.bytes[i]!}"
      checked := checked + 1
  unless actual.data.status == expected.data.status do
    throw s!"captured endpoint flags after {checked} matching bytes: Kraken={repr actual.data.status}, kernel={repr expected.data.status}"
  unless actual.data.pushFlags == expected.data.pushFlags && actual.data.system.cpl==0 do
    throw s!"captured endpoint system flags after {checked} matching bytes: Kraken={actual.data.pushFlags}, kernel={expected.data.pushFlags}"
  return checked

def compareReturn (snapshot : Snapshot) (actual : Run) : Except String Nat := do
  unless snapshot.executedPCs == actual.pcs do
    throw "captured instruction sequence differs from Kraken execution"
  compareEndpoint snapshot.returned actual.state

def run (input : ProbeInput) (snapshot : Snapshot) (layout : Json) : Except String Json := do
  unless snapshot.executionMode == "sequential" do
    throw "captured replay requires the declared sequential environment; ordinary execution may interleave interrupts"
  unless (← input.trace.getObjValAs? String "id") == snapshot.trace && input.operation == snapshot.operation &&
      snapshot.completedOperations.toList == List.range snapshot.operation do throw "snapshot workload/invocation mismatch"
  let world ← replayPrefix input.trace input.operation
  let some d := world.wg.dev | throw "recorded source prefix has no device"
  let initial ← snapshot.initial.registers.state (← loadMemory snapshot.initial.blocks)
  let n ← names input snapshot layout initial d
  let frame ← callFrame input snapshot layout initial
  let mut coverage := #[]
  for i in [:snapshot.initial.coverageUsed] do
    coverage := coverage.push (← readNat initial (frame.coverage + 8*(i+1)) 8)
  let session : Session := {names := n, world, binary := {state := initial, coverage}}
  let mut outcomes := #[]
  for seed in [(0 : UInt64), 0xffffffffffffffff] do
    let (after, report) ← (lookupFrom input seed session input.query [.handshake] initial frame).mapError
      (fun e => s!"captured invocation, seed {seed}: {e}")
    assertMemory n input.offsets (← loadMemory snapshot.returned.blocks) after.world
    let checked ← compareReturn snapshot after.binary
    outcomes := outcomes.push (Json.mkObj [("seed", toJson seed.toNat), ("call", report),
      ("captured_return_bytes_checked", toJson checked),
      ("coverage_added", toJson (after.binary.coverage.size - coverage.size))])
  return Json.mkObj [("status", toJson "pass"), ("origin", toJson "actual QEMU entry and return; no relocation or heap construction"),
    ("environment", toJson "sequential QEMU stepping, IRQs and timers deferred within call"),
    ("trace", toJson snapshot.trace), ("operation", toJson snapshot.operation),
    ("entry_preempt", toJson frame.entryPreempt), ("runs", toJson outcomes)]

end Binary.Pair.Capture
