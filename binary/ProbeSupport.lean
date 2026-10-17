import Image
import Leanux.Runner
import Layouts

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
  peerHandshake : Nat
  handshakeEntry : Nat
  keypairEntry : Nat
  peerRefcount : Nat
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

/-- Replay complete recorded operations with executeTrace's entry settings.
    Each concrete probe separately validates its selected corpus case. -/
def replayRecordedPrefix (j : Json) (count : Nat) : Except String Leanux.World := do
  let t ← Leanux.Runner.parseTrace j
  unless t.ops.size > count && t.hidden.isSome do
    throw "probe requires a recorded prefix and a following operation"
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

def replayPrefix (j : Json) (count : Nat) : Except String Leanux.World := do
  unless count == 3 do throw "index probe requires the recorded three-operation prefix"
  replayRecordedPrefix j count

def tableAddr : Nat := 0x100000
def peerAddr (id : Leanux.WG.PeerId) : Nat := 0x600000 + id * 0x1000

def entryAddr (e : Leanux.WG.IndexEntry) (o : Offsets) : Except String Nat := do
  match e.owner with
  | .handshake id => return peerAddr id + o.peerHandshake + o.handshakeEntry
  | .keypair id => return 0x700000 + id * 0x1000 + o.keypairEntry

def ownerWord (d : Leanux.WG.Device) (owner : Leanux.WG.IndexOwner) : Except String (Option Nat) := do
  match owner with
  | .handshake id =>
    let some p := d.peers.get? id | throw "handshake owner missing"
    return p.handshakeEntryPeer
  | .keypair id =>
    let some k := d.keypairs.get? id | throw "keypair owner missing"
    return k.peer

def nullablePeerAddr (peer : Option Nat) : Nat := peer.map peerAddr |>.getD 0

def outputAddr : Nat := 0x300000
def stackAddr : Nat := 0x400800
def stopAddr : Nat := 0x500000

def put (m : DataMem) (a size v : Nat) : DataMem :=
  m.storeInt (.ofNat 64 a) size v

/-- Heap materialization is generated from the mirror list and DWARF offsets.
    Synthetic addresses are related to identities, not claimed to be kernel pointers. -/
def materialize (d : Leanux.WG.Device) (o : Offsets) (preempt : Nat) : Except String DataMem := do
  let entries := d.indexTable
  let mut m : DataMem := (List.replicate o.tableSize (0 : UInt8)).At (.ofNat 64 tableAddr)
  m := m.storeBytes (.ofNat 64 (stackAddr - 0x800)) (List.replicate 0x810 0)
  m := put m stackAddr 8 stopAddr
  m := put m outputAddr 8 0xfeedface
  m := put m preempt 4 0
  let addresses ← entries.mapM (entryAddr · o)
  unless addresses.eraseDups.length == addresses.length do
    throw "index entries alias the same embedded object"
  for (e, i) in entries.zipIdx do
    let addr ← entryAddr e o
    m := m.storeBytes (.ofNat 64 addr) (List.replicate o.entrySize 0)
    let bucket := e.index % 8192
    let bucketAddr := tableAddr + o.buckets + bucket * o.headSize + o.first
    let before := (entries.take i).zipIdx.filter (fun (e, _) => e.index % 8192 == bucket)
    let after := (entries.zipIdx.drop (i+1)).find? (fun (e, _) => e.index % 8192 == bucket)
    let prevAddr ← match before.getLast? with
      | none => pure bucketAddr
      | some (previous, _) => (entryAddr previous o).map (fun a => a + o.hash + o.next)
    let nextAddr ← match after with
      | none => pure 0
      | some (next, _) => (entryAddr next o).map (fun a => a + o.hash)
    if before.isEmpty then m := put m bucketAddr 8 (addr + o.hash)
    m := put m (addr + o.peer) 8 (nullablePeerAddr (← ownerWord d e.owner))
    m := put m (addr + o.hash + o.next) 8 nextAddr
    m := put m (addr + o.hash + o.pprev) 8 prevAddr
    m := put m (addr + o.kind) 4 (if e.kind == .handshake then 1 else 2)
    m := put m (addr + o.index) 4 e.index
  return m

def keypairAddr (id : Leanux.WG.KeypairId) : Nat := 0x700000 + id * 0x1000

/-- Materialize full keypair fields, including unselected objects and the
    peer's three slots. Reject values that cannot satisfy the exact equations. -/
def materializePeers (d : Leanux.WG.Device) (o : Offsets) (m : DataMem) : Except String DataMem := do
  for e in d.indexTable do
    let word ← ownerWord d e.owner
    if let some id := word then
      unless d.peers.contains id do throw "entry names an absent peer"
  let mut m := m
  for (id, p) in d.peers.toList do
    unless p.refcount < 2^32 do throw "peer refcount is not a 32-bit value"
    m := put m (peerAddr id + o.peerRefcount) 4 p.refcount
    if let some pid := p.handshakeEntryPeer then
      unless d.peers.contains pid do throw "handshake word names an absent peer"
    m := put m (peerAddr id + o.peerHandshake + o.handshakeEntry + o.peer) 8
      (nullablePeerAddr p.handshakeEntryPeer)
    for (slot, kid) in [(Binary.Layouts.slots_current_keypair, p.keypairCurrent),
        (Binary.Layouts.slots_previous_keypair, p.keypairPrevious),
        (Binary.Layouts.slots_next_keypair, p.keypairNext)] do
      let address ← match kid with
        | none => pure 0
        | some id => do
          unless d.keypairs.contains id do throw "peer slot names an absent keypair"
          pure (keypairAddr id)
      m := put m (peerAddr id + Binary.Layouts.peer_keypairs + slot) 8 address
  for (id, k) in d.keypairs.toList do
    let a := keypairAddr id
    if let some pid := k.peer then
      unless d.peers.contains pid do throw "keypair names an absent peer"
    unless k.internalId < 2^64 && k.sendingCounter < 2^64 &&
        k.receivingCounter.counter < 2^64 && k.remoteIndex < 2^32 && k.refcount < 2^32 do
      throw "keypair field is outside its physical word width"
    m := put m (a + Binary.Layouts.keypair_entry + Binary.Layouts.entry_peer) 8 (nullablePeerAddr k.peer)
    m := put m (a + Binary.Layouts.keypair_internal_id) 8 k.internalId
    m := put m (a + Binary.Layouts.keypair_sending_counter) 8 k.sendingCounter
    m := put m (a + Binary.Layouts.keypair_remote_index) 4 k.remoteIndex
    m := put m (a + Binary.Layouts.keypair_refcount) 4 k.refcount
    m := put m (a + Binary.Layouts.keypair_i_am_the_initiator) 1 (if k.iAmTheInitiator then 1 else 0)
    for (offset, key) in [(Binary.Layouts.keypair_sending, k.sending),
        (Binary.Layouts.keypair_receiving, k.receiving)] do
      unless key.key.length == 32 do throw "symmetric key is not 32 bytes"
      m := m.storeBytes (.ofNat 64 (a + offset + Binary.Layouts.symmetric_key)) key.key
      m := put m (a + offset + Binary.Layouts.symmetric_birthdate) 8 key.birthdate.toBitVec.toNat
      m := put m (a + offset + Binary.Layouts.symmetric_is_valid) 1 (if key.isValid then 1 else 0)
    let replay := a + Binary.Layouts.keypair_receiving_counter
    m := put m (replay + Binary.Layouts.replay_counter) 8 k.receivingCounter.counter
    unless k.receivingCounter.backtrack.size == Binary.Layouts.replayWords do
      throw "keypair replay bitmap has the wrong size"
    for i in [:k.receivingCounter.backtrack.size] do
      unless k.receivingCounter.backtrack[i]! < 2^64 do throw "replay bitmap word exceeds 64 bits"
      m := put m (replay + Binary.Layouts.replay_backtrack + i * Binary.Layouts.replayWordBytes)
        Binary.Layouts.replayWordBytes k.receivingCounter.backtrack[i]!
  return m

def coverageAddr : Nat := 0x900000
def coverageBytes : Nat := 0x2000

/-- Concrete service-readiness fixture. KCOV_TRACE_PC is mode 2; comparison
    callbacks run their real early-return path in this capture mode. -/
def materializeServices (m : DataMem) : DataMem := Id.run do
  let task := 0x800000
  let mut m := put m 0xffffffff81cc85c0 8 task
  m := put m 0xffffffff81cc85e0 2 0
  m := put m (task + 0x6e0) 4 2
  m := put m (task + 0x6e4) 4 (coverageBytes / 8)
  m := put m (task + 0x6e8) 8 coverageAddr
  m := put m (task + 0x704) 4 0
  return m.storeBytes (.ofNat 64 coverageAddr) (List.replicate coverageBytes 0)

structure Run where
  state : MachineState
  pcs : Array Nat := #[]
  history : Array MachineState := #[]
  coverage : Array Nat := #[]
  comparisons : Array (Nat × Nat × Nat) := #[]
  writes : Array (Nat × Nat) := #[]
  reads : Array (Nat × Nat) := #[]
  undefinedCount : Nat := 0

/-- Same deterministic undefined-value choice mechanism as Kraken's evaluator.
    Two seeds are run below; this is testing, not universal quantification. -/
partial def effects (seed : UInt64) (r : Run) : Effects → Except String Run
  | .done s => pure {r with state := s}
  | .require_read_access a w k => do
    unless (r.state.data.dmem.loadBytes a w.bytes).isSome do throw s!"unmapped read {a}"
    effects seed {r with reads := r.reads.push (a.toNat, w.bytes)} (k ())
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
    (fun d => .done ⟨d, .ofNat (pc+size)⟩) (fun p d => .done ⟨d, p⟩)) >>= fun next =>
      pure {next with history := r.history.push next.state}

def runUntil (instructions : Array Instruction) (labels : Array (String × Nat))
    (hooks : Array (Nat × String)) (preempt : Nat) (initial : MachineState) (seed : UInt64)
    (actualServices : Bool) (budget entryPreempt : Nat)
    (stops : Array Nat) (prior : Option Run := none)
    (returnPC : Nat := stopAddr) : Except String Run := do
  -- Labels is total in Kraken. Check every reference before constructing it;
  -- its default is unreachable for this validated one-instruction input format.
  for i in instructions do
    for suffix in (i.asm.splitOn "L_").tail do
      let name := "L_" ++ suffix.trimAscii.toString
      let some address := Binary.Image.canonicalAddress name
        | throw s!"malformed label at {i.pc}: {name}"
      let some (_, value) := labels.find? (·.1 == name)
        | throw s!"missing label at {i.pc}: {name}"
      unless value == address.toBitVec.toNat do throw s!"label address mismatch: {name}"
  let _ : Labels := ⟨fun l => .ofNat ((labels.find? (·.1 == l)).map (·.2) |>.getD 0)⟩
  let mut r : Run := prior.getD {state := initial, history := #[initial]}
  for tick in [:budget] do
    let pc := r.state.pc.toBitVec.toNat
    if pc == returnPC || (tick > 0 && stops.contains pc) then return r
    if let some (_, name) := hooks.find? (·.1 == pc) then
      let ra ← readNat r.state r.state.data.regs.rsp.toNat 8
      if name == "__sanitizer_cov_trace_pc" then
        r := {r with coverage := r.coverage.push ra}
      else if name == "__sanitizer_cov_trace_cmp4" || name == "__sanitizer_cov_trace_const_cmp4" ||
          name == "__sanitizer_cov_trace_const_cmp1" || name == "__sanitizer_cov_trace_cmp1" ||
          name == "__sanitizer_cov_trace_cmp8" then
        let bits := if name == "__sanitizer_cov_trace_cmp8" then 64
          else if name == "__sanitizer_cov_trace_const_cmp1" || name == "__sanitizer_cov_trace_cmp1" then 8 else 32
        let comparison := (ra, r.state.data.regs.rdi.toNat % (2^bits), r.state.data.regs.rsi.toNat % (2^bits))
        r := {r with comparisons := r.comparisons.push comparison}
      else if name == "__local_bh_enable_ip" then
        if !actualServices then
          unless r.state.data.regs.rsi == 512 && (← readNat r.state preempt 4) == entryPreempt + 512 do
            throw "environment summary requires one balanced BH-disable and no pending work"
          r := {r with state := {r.state with data := {r.state.data with
            dmem := put r.state.data.dmem preempt 4 entryPreempt}}}
      else
        throw s!"unclassified or unreached-path call: {name}"
      if !actualServices then
        r ← interpret seed r (.regular .W64 .W64 .ret) pc 1
        continue
    let some i := instructions.find? (·.pc == pc) | throw s!"PC outside decoded functions: {pc}"
    let [.instr op] ← Kraken.X64.Parser.parse i.asm | throw s!"not one instruction at {pc}: {i.asm}"
    r := {r with pcs := r.pcs.push pc}
    r ← interpret seed r op pc i.size
  throw "instruction budget exhausted"


def runProgram (instructions : Array Instruction) (labels : Array (String × Nat))
    (hooks : Array (Nat × String)) (preempt : Nat) (initial : MachineState) (seed : UInt64)
    (actualServices : Bool) (budget entryPreempt : Nat) : Except String Run :=
  runUntil instructions labels hooks preempt initial seed actualServices budget entryPreempt #[]

def runMachine (input : ProbeInput) (initial : MachineState) (seed : UInt64)
    (actualServices : Bool := false) : Except String Run :=
  runProgram input.instructions input.labels input.hooks input.preempt initial seed actualServices 1000 0
