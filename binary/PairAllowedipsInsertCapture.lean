import PairAllowedipsMutation
import PairAllowedipsCapture

namespace Binary.Pair.Allowedips.Capture
open Lean Leanux
open Binary.Pair.Capture (Endpoint loadMemory)

structure Service where
  initial : Endpoint
  returned : Endpoint
  allocation : Nat
  returnPC : Nat
  deriving FromJson

structure Snapshot where
  kernel : Json
  image_sha256 : String
  kraken : String
  executionMode : String
  family : Nat
  key : Nat
  cidr : Nat
  table : Nat
  peer : Nat
  task : Nat
  coverage : Nat
  capacity : Nat
  coverageUsed : Nat
  instructionBudget : Nat
  initial : Endpoint
  returned : Endpoint
  services : Array Service
  executedPCs : Array Nat
  bulkBlocks : Array Trie.Capture.BulkBlock
  allocationRecord : Nat × String
  deriving FromJson

def outcomeRecord (snapshot : Snapshot) : Except String HiddenRecord := do
  let (site,hex) := snapshot.allocationRecord
  unless site == 77 && hex.length == 80 do throw "capture.allocation-record"
  let digits := hex.toList.toArray
  let digit (c : Char) : Except String Nat :=
    if '0' ≤ c && c ≤ '9' then .ok (c.toNat-'0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then .ok (c.toNat-'a'.toNat+10)
    else .error "capture.invalid-hex"
  let mut bytes := []
  for i in [:40] do
    let a ← digit digits[2*i]!
    let b ← digit digits[2*i+1]!
    bytes := bytes++[.ofNat (16*a+b)]
  unless bytes.headD 0 == 1 do throw "capture.expected-successful-allocation"
  return ⟨site,bytes⟩

/-- The external service transition is supplied from QEMU. It may write its
own stack, coverage area and the newly returned allocation only. Every captured
protected byte is checked before and after, never repaired from the endpoint. -/
def allocator (input : Input) (snapshot : Snapshot) (r : Run) (names : Names)
    (released : List Nat) (records : List HiddenRecord) :
    Except String (Run × Names × List Nat × List HiddenRecord) := do
  let #[service] := snapshot.services | throw "capture.service-count"
  unless r.state.pc.toBitVec.toNat == input.alloc && names.trie.nodes.isEmpty && names.nextNode == 0 do
    throw "capture.expected-first-allocation"
  let _ ← Binary.Pair.Capture.compareEndpoint service.initial r.state
  let ra ← readNat r.state r.state.data.regs.rsp.toNat 8
  unless ra == service.returnPC && input.allocationReturns.contains (ra,7) &&
      service.returned.registers.rip == ra && service.returned.registers.rsp == r.state.data.regs.rsp.toNat+8 &&
      service.returned.registers.rax == service.allocation && service.allocation > 0 do
    throw "capture.allocator-abi"
  unless r.state.data.regs.rdi.toNat == (← readNat r.state input.cacheWord 8) &&
      r.state.data.regs.rsi.toNat == 0xdc0 do throw "capture.allocator-arguments"
  let record::rest := records | throw "capture.missing-outcome"
  unless record == (← outcomeRecord snapshot) do throw "capture.outcome-differs"
  let nodeSize := input.lookup.offsets.nodeSize
  unless service.allocation%8 == 0 && service.allocation+nodeSize < 2^64 do throw "capture.allocation-range"
  for i in [:nodeSize] do
    unless (r.state.data.dmem.get? (.ofNat 64 (service.allocation+i))).isNone do
      throw "capture.allocation-overlaps-entry"
  let mut memory := r.state.data.dmem
  let scratch := snapshot.initial.registers.rsp-2048
  let scratchSize := service.initial.registers.rsp-scratch
  for block in service.returned.blocks do
    for i in [:block.bytes.size] do
      let address := block.address+i
      let byte := block.bytes[i]!
      unless address < 2^64 && byte < 256 do throw "capture.invalid-service-byte"
      let writable := Trie.within address 1 scratch scratchSize ||
        Trie.within address 1 snapshot.coverage (snapshot.capacity*8) ||
        Trie.within address 1 service.allocation nodeSize
      if writable then memory := memory.insert (.ofNat 64 address) byte.toUInt8
      else unless memory.get? (.ofNat 64 address) == some byte.toUInt8 do
        throw s!"capture.service-changed-protected-byte {address}"
  let state ← service.returned.registers.state memory
  for reg in [Reg64.rbx,.rbp,.r12,.r13,.r14,.r15] do
    unless state.data.regs.get64 reg == r.state.data.regs.get64 reg do throw "capture.service-callee-save"
  unless state.data.system.bits[9] == r.state.data.system.bits[9] do throw "capture.service-interrupt-state"
  let some zeros := memory.loadBytes (.ofNat 64 service.allocation) nodeSize | throw "capture.allocation-missing"
  unless zeros.all (· == 0) do throw "capture.allocation-not-zero"
  let used ← readNat state snapshot.coverage 8
  unless used < snapshot.capacity do throw "capture.service-coverage-count"
  let mut coverage := #[]
  for i in [:used] do coverage := coverage.push (← readNat state (snapshot.coverage+8*(i+1)) 8)
  return ({r with state,coverage}, {names with
    nextNode := 1
    trie := {names.trie with nodes := [(0,service.allocation)]}},released,rest)

def createdPeer : World := {
  ambient := {env := Runner.harnessEnv,timing := Env.timing},tasks := Runner.initialTasks 1024 false false false,
  fs := {},wg := {dev := some {ifindex := 1,ifname := "wg0",peers :=
    ({} : Std.TreeMap WG.PeerId WG.Peer).insert 0 {
      remoteStatic := List.replicate 32 0,presharedKey := List.replicate 32 0,
      precomputedStaticStatic := List.replicate 32 0,internalId := 0}}} }

/-- `setPeerCmd` takes a temporary reference after successful creation and
before traversing allowed IPs. Execute that source operation; do not infer its
count from the captured memory that the independent assertion will compare. -/
def source : Except String World := do
  let (_,world) ← (liftWG (WG.peerGet 0)).run createdPeer |>.mapError Stop.message
  return world

def run (input : Input) (snapshot : Snapshot) (memory : DataMem) : Except String Json := do
  unless (← snapshot.kernel.getObjValAs? Bool "checked") &&
      (← snapshot.kernel.getObjValAs? String "expected") == TrustBase.kernelIdentity &&
      (← snapshot.kernel.getObjValAs? String "actual") == TrustBase.kernelIdentity &&
      snapshot.image_sha256 == TrustBase.elfSha256 && snapshot.kraken == TrustBase.krakenCommit do
    throw "capture.image-or-semantics-identity"
  unless snapshot.executionMode == "sequential" && snapshot.family == 4 do throw "capture.mode-or-family"
  let initial ← snapshot.initial.registers.state memory
  let names : Names := ⟨snapshot.table,⟨[],[(0,snapshot.peer)]⟩,0⟩
  let preempt ← readNat initial input.lookup.preempt 4
  let input := {input with lookup := {input.lookup with entryPreempt := preempt,budget := snapshot.instructionBudget}}
  let frame : CallFrame := {
    stack := initial.data.regs.rsp.toNat,returnPC := (← readNat initial initial.data.regs.rsp.toNat 8),
    coverage := snapshot.coverage,coverageSize := snapshot.capacity*8,task := snapshot.task,
    entryPreempt := preempt,budget := snapshot.instructionBudget}
  let mut coverage := #[]
  for i in [:snapshot.coverageUsed] do coverage := coverage.push (← readNat initial (snapshot.coverage+8*(i+1)) 8)
  let session : Session := ⟨names,← source,{state := initial,coverage},[]⟩
  let mut reports := #[]
  for seed in [(0 : UInt64),0xffffffffffffffff] do
    let (after,report) ← invokeFrom input seed session 4 snapshot.key snapshot.cidr 0 [← outcomeRecord snapshot]
      initial frame (allocator input snapshot)
    unless after.binary.pcs == snapshot.executedPCs do throw "capture.instruction-sequence"
    let bytes ← Binary.Pair.Capture.compareEndpoint snapshot.returned after.binary.state
    reports := reports.push (Json.mkObj [("seed",toJson seed.toNat),("call",report),("compared_bytes",toJson bytes)])
  return Json.mkObj [("status",toJson "pass"),("runs",toJson reports),
    ("service",toJson "captured generic allocator transition; allocator body not interpreted or proved")]

end Binary.Pair.Allowedips.Capture
