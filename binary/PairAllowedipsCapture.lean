import PairAllowedips
import PairCapture

namespace Binary.Pair.Trie.Capture
open Lean Leanux Leanux.WG
open Binary.Pair.Capture (Endpoint loadMemory member)

structure BulkBlock where
  address : Nat
  file : String
  size : Nat
  deriving FromJson

structure Snapshot extends Binary.Pair.Capture.Snapshot where
  headers : Array Binary.Pair.Capture.Endpoint
  bulkBlocks : Array BulkBlock := #[]
  deriving FromJson

/-- The transport format stores large captured allocations as raw bytes.
This loader still installs each actual byte in Kraken's ordinary memory. -/
def loadBulk (memory : DataMem) (blocks : Array (Nat × ByteArray)) : Except String DataMem := do
  let mut memory := memory
  for (base,bytes) in blocks do
    unless base > 0 && base+bytes.size ≤ 2^64 do throw "NULL or wrapping bulk capture"
    for i in [:bytes.size] do
      let a := BitVec.ofNat 64 (base+i)
      let b := bytes[i]!
      if let some old := memory.get? a then
        unless old == b do throw "overlapping bulk capture bytes disagree"
      memory := memory.insert a b
  return memory

/-- Bootstrap identities from public keys and paths from the two independently
read roots. Field equality is checked later by the shared reconstruction, and
no expected source value is ever installed in binary memory. -/
def names (input : AllowedipsProbe.Input) (snapshot : Snapshot) (layout : Json)
    (initial : MachineState) (d : Device) : Except String Names := do
  let keyOffset := (← member layout "wg_peer" "handshake") +
    (← member layout "noise_handshake" "remote_static")
  let mut peers := []
  for (id, peer) in d.peers.toList do
    let candidates := snapshot.initial.peers.filter
      (fun p => p.publicKey.toList == peer.remoteStatic.map UInt8.toNat)
    unless candidates.size == 1 do throw s!"peer[{id}]: public key is not unique in capture"
    let some p := candidates[0]? | throw "peer identity missing"
    let some bytes := initial.data.dmem.loadBytes (.ofNat 64 (p.address+keyOffset)) 32
      | throw "peer public key bytes missing"
    unless bytes.map UInt8.toNat == p.publicKey.toList do throw "peer public key metadata differs from memory"
    peers := peers ++ [(id,p.address)]
  unless peers.length == snapshot.initial.peers.size do throw "uninterpreted captured peer"
  let base := snapshot.initial.device + (← member layout "wg_device" "peer_allowedips")
  let root4 ← readNat initial (base + (← member layout "allowedips" "root4")) 8
  let root6 ← readNat initial (base + (← member layout "allowedips" "root6")) 8
  let mut todo := [(d.peerAllowedips.root4,root4),(d.peerAllowedips.root6,root6)]
  let mut pairs : List (Nat × Nat) := []
  for _ in [:2*d.nodes.size+2] do
    let (id,ptr) :: rest := todo | break
    todo := rest
    match id with
    | none => unless ptr == 0 do throw "trie shape: unexpected binary child/root"
    | some id =>
      unless ptr != 0 && !pairs.any (fun p => p.1 == id || p.2 == ptr) do
        throw "trie shape: NULL, repeated node or shared child"
      let some node := d.nodes.get? id | throw "source trie names missing node"
      unless node.bit.size == 2 do throw "source node has invalid child count"
      pairs := pairs ++ [(id,ptr)]
      for side in [:2] do
        todo := todo ++ [(node.bit[side]!, ← readNat initial (ptr+input.offsets.children+8*side) 8)]
  unless todo.isEmpty && pairs.length == d.nodes.size do throw "trie shape: incomplete identity closure"
  let nodes ← d.nodes.toList.mapM fun (id,_) => do
    let some (_,a) := pairs.find? (·.1 == id) | throw "source node unreachable from captured roots"
    pure (id,a)
  return {nodes,peers}

def frame (input : AllowedipsProbe.Input) (snapshot : Snapshot) (layout : Json)
    (s : MachineState) : Except String (CallFrame × CommonBitsCoverage.Context) := do
  let e := snapshot.initial
  let pcpu := input.preempt - (← member layout "pcpu_hot" "preempt_count")
  let currentTask := pcpu + (← member layout "pcpu_hot" "current_task")
  let pending := pcpu + (← member layout "pcpu_hot" "softirq_pending")
  unless (← readNat s currentTask 8) == e.task && (← readNat s (e.task+0x6e0) 4) == 2 &&
      (← readNat s (e.task+0x6e4) 4) == e.capacity &&
      (← readNat s (e.task+0x6e8) 8) == e.coverage &&
      (← readNat s e.coverage 8) == e.coverageUsed do throw "captured service metadata differs from memory"
  unless e.coverageUsed < e.capacity && e.coverageCapturedWords == e.capacity do
    throw "checked callback boundary requires the complete captured coverage allocation"
  unless 0 < snapshot.instructionBudget && snapshot.instructionBudget ≤ 1000000 do throw "invalid capture budget"
  let preempt ← readNat s input.preempt 4
  let soft ← readNat s (e.task+0x704) 4
  let returnPC ← readNat s s.data.regs.rsp.toNat 8
  let f : CallFrame := {
    stack := s.data.regs.rsp.toNat, returnPC := returnPC,
    entryPreempt := preempt, coverage := e.coverage, coverageSize := e.capacity*8,
    task := e.task, currentTask := currentTask, pending := pending, budget := snapshot.instructionBudget }
  let c : CommonBitsCoverage.Context :=
    ⟨⟨.ofNat 64 e.task,.ofNat 64 e.coverage,.ofNat 32 e.capacity,2,.ofNat 32 soft⟩,.ofNat 32 (preempt+512)⟩
  return (f,c)

def reject (label needle : String) (check : Except String Unit) : Except String Json := do
  match check with
  | .ok () => throw s!"control {label} was accepted"
  | .error e =>
    unless (e.splitOn needle).length > 1 do throw s!"control {label} failed for the wrong reason: {e}"
    return Json.mkObj [("control",toJson label),("detected",toJson e)]

/-- At the pinned header the last flag writer is XOR on the first visit and
TEST on later visits. Kraken gives AF an undefined value for both. Compare
the other five flags, all registers and all sampled bytes without changing
the machine passed to execution or the reconstruction assertion. -/
def compareHeader (endpoint : Binary.Pair.Capture.Endpoint) (actual : MachineState) : Except String Nat := do
  unless actual.pc == AllowedipsImage.Lookup.entry+0xd5 do throw "header comparison at wrong PC"
  let observed := {actual with data := {actual.data with
    status := {actual.data.status with af := endpoint.registers.eflags.testBit 4}}}
  Binary.Pair.Capture.compareEndpoint endpoint observed

def run (input : AllowedipsProbe.Input) (snapshot : Snapshot) (layout : Json)
    (initialMemory : DataMem) : Except String Json := do
  unless snapshot.executionMode == "sequential" do throw "capture is not sequential"
  unless (← input.trace.getObjValAs? String "id") == snapshot.trace && input.operation == snapshot.operation &&
      snapshot.completedOperations.toList == List.range snapshot.operation do throw "capture workload/prefix differs"
  let trace ← Leanux.Runner.parseTrace input.trace
  let some (.wgXmit family key _ _) := trace.ops[input.operation]? | throw "capture operation is not wg_xmit"
  let prior ← replayRecordedPrefix input.trace input.operation
  let w := {prior with steps := #[], hidden := some [], netRxSection := 0, netRxSections := 0}
  let some d := w.k.wg | throw "source prefix has no device"
  let width := if family == 4 then 32 else 128
  let root := if width == 32 then d.peerAllowedips.root4 else d.peerAllowedips.root6
  let initial ← snapshot.initial.registers.state initialMemory
  let n ← names input snapshot layout initial d
  let (f,c) ← frame input snapshot layout initial
  let input := {input with entryPreempt := f.entryPreempt, budget := f.budget}
  let mut coverage := #[]
  for i in [:snapshot.initial.coverageUsed] do
    coverage := coverage.push (← readNat initial (f.coverage+8*(i+1)) 8)
  let mut controls := #[]
  let some (id,peerAddress) := n.peers.head? | throw "capture has no peer identity"
  let some peer := d.peers.get? id | throw "capture names an absent peer"
  controls := controls.push (← reject "peer-count" "trie.counts"
    (assertAt n input.offsets (put initial.data.dmem (peerAddress+input.offsets.peerRefcount) 4 (peer.refcount+1)) w))
  let rootAddress := snapshot.initial.device + (← member layout "wg_device" "peer_allowedips") +
    (← member layout "allowedips" (if width == 32 then "root4" else "root6"))
  controls := controls.push (← reject "device-root" "trie shape"
    ((names input snapshot layout {initial with data := {initial.data with dmem := put initial.data.dmem rootAddress 8 0}} d).map (fun _ => ())))
  let mut outcomes := #[]
  for seed in [(0 : UInt64), 0xffffffffffffffff] do
    let (final,r,report) ← (lookupFrom n input seed initial f c coverage w root width key).mapError
      (fun e => s!"captured paired lookup, seed {seed}: {e}")
    let headers := r.history.filter (fun s => s.pc.toBitVec.toNat == input.entry+0xd5)
    unless headers.size == snapshot.headers.size do throw "captured loop-header count differs"
    let mut headerBytes := 0
    for i in [:headers.size] do
      let some captured := snapshot.headers[i]? | throw "missing captured header"
      let some actual := headers[i]? | throw "missing replay header"
      headerBytes := headerBytes + (← (compareHeader captured actual).mapError
        (fun e => s!"seed {seed}, captured header {i}: {e}"))
      if seed == 0 && i == 0 then
        let wrong := {captured with registers := {captured.registers with eflags := captured.registers.eflags ^^^ 64}}
        controls := controls.push (← reject "header-defined-flag" "endpoint flags"
          ((compareHeader wrong actual).map (fun _ => ())))
      -- Independently apply reconstruction to QEMU's own header bytes too.
      assertAt n input.offsets (← loadMemory captured.blocks) w
    assertAt n input.offsets (← loadMemory snapshot.returned.blocks) final
    let checked ← (Binary.Pair.Capture.compareReturn snapshot.toSnapshot r).mapError
      (fun e => s!"seed {seed}, captured return: {e}")
    if seed == 0 then
      controls := controls.push (← reject "instruction-sequence" "instruction sequence"
        ((Binary.Pair.Capture.compareReturn {snapshot.toSnapshot with executedPCs := #[]} r).map (fun _ => ())))
      let returned := snapshot.returned
      let wrong := {returned with registers := {returned.registers with rax := returned.registers.rax ^^^ 1}}
      controls := controls.push (← reject "return-result" "Reg64.rax"
        ((Binary.Pair.Capture.compareReturn {snapshot.toSnapshot with returned := wrong} r).map (fun _ => ())))
    outcomes := outcomes.push (Json.mkObj [("seed",toJson seed.toNat),("call",report),
      ("captured_headers",toJson headers.size),("captured_header_bytes_checked",toJson headerBytes),
      ("captured_return_bytes_checked",toJson checked),
      ("coverage_added",toJson (r.coverage.size-coverage.size))])
  return Json.mkObj [("status",toJson "pass"),("width",toJson width),
    ("origin",toJson "actual QEMU entry, headers and return; no relocated or constructed bytes"),
    ("environment",toJson "sequential stepping; IRQs and timers deferred during call"),
    ("trace",toJson snapshot.trace),("operation",toJson snapshot.operation),
    ("entry_preempt",toJson f.entryPreempt),("runs",toJson outcomes),("controls",toJson controls)]

end Binary.Pair.Trie.Capture
