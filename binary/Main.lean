import Kraken.X64.Parser
import Kraken.X64.Semantics
import Leanux.Runner
import LookupObservation
import Layouts
import TrustBase

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
def peerAddr (id : Leanux.WG.PeerId) : Nat := 0x600000 + id * 0x1000

def entryAddr (e : Leanux.WG.IndexEntry) (o : Offsets) : Except String Nat := do
  match e.kind with
  | .handshake => return peerAddr e.peer + o.peerHandshake + o.handshakeEntry
  | .keypair =>
    let some id := e.keypair | throw "keypair entry has no keypair identity"
    return 0x700000 + id * 0x1000 + o.keypairEntry
def outputAddr : Nat := 0x300000
def stackAddr : Nat := 0x400800
def stopAddr : Nat := 0x500000

def put (m : DataMem) (a size v : Nat) : DataMem :=
  m.storeInt (.ofNat 64 a) size v

/-- Heap materialization is generated from the mirror list and DWARF offsets.
    Synthetic addresses are related to identities, not claimed to be kernel pointers. -/
def materialize (entries : List Leanux.WG.IndexEntry) (o : Offsets) (preempt : Nat) : Except String DataMem := do
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
    m := put m (addr + o.peer) 8 (0x600000 + e.peer * 0x1000)
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
    unless d.peers.contains e.peer do throw "entry names an absent peer"
  let mut m := m
  for (id, p) in d.peers.toList do
    unless p.refcount < 2^32 do throw "peer refcount is not a 32-bit value"
    m := put m (peerAddr id + o.peerRefcount) 4 p.refcount
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
    unless d.peers.contains k.peer do throw "keypair names an absent peer"
    for e in d.indexTable do
      if e.kind == .keypair && e.keypair == some id && e.peer != k.peer then
        throw "index entry and keypair disagree on their shared peer word"
    unless k.internalId < 2^64 && k.sendingCounter < 2^64 &&
        k.receivingCounter.counter < 2^64 && k.remoteIndex < 2^32 && k.refcount < 2^32 do
      throw "keypair field is outside its physical word width"
    m := put m (a + Binary.Layouts.keypair_entry + Binary.Layouts.entry_peer) 8 (peerAddr k.peer)
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
    (fun d => .done ⟨d, .ofNat (pc+size)⟩) (fun p d => .done ⟨d, p⟩)) >>= fun next =>
      pure {next with history := r.history.push next.state}

def runMachine (input : ProbeInput) (initial : MachineState) (seed : UInt64)
    (actualServices : Bool := false) : Except String Run := do
  let _ : Labels := ⟨fun l => .ofNat ((input.labels.find? (·.1 == l)).map (·.2) |>.getD 0)⟩
  let mut r : Run := {state := initial, history := #[initial]}
  for _ in [:1000] do
    let pc := r.state.pc.toBitVec.toNat
    if pc == stopAddr then return r
    if let some (_, name) := input.hooks.find? (·.1 == pc) then
      let ra ← readNat r.state r.state.data.regs.rsp.toNat 8
      if name == "__sanitizer_cov_trace_pc" then
        r := {r with coverage := r.coverage.push ra}
      else if name == "__sanitizer_cov_trace_cmp4" || name == "__sanitizer_cov_trace_const_cmp4" ||
          name == "__sanitizer_cov_trace_const_cmp1" then
        let bits := if name == "__sanitizer_cov_trace_const_cmp1" then 8 else 32
        let comparison := (ra, r.state.data.regs.rdi.toNat % (2^bits), r.state.data.regs.rsi.toNat % (2^bits))
        r := {r with comparisons := r.comparisons.push comparison}
      else if name == "__local_bh_enable_ip" then
        if !actualServices then
          unless r.state.data.regs.rsi == 512 && (← readNat r.state input.preempt 4) == 512 do
            throw "environment summary requires one balanced BH-disable and no pending work"
          r := {r with state := {r.state with data := {r.state.data with
            dmem := put r.state.data.dmem input.preempt 4 0}}}
      else
        throw s!"unclassified or unreached-path call: {name}"
      if !actualServices then
        r ← interpret seed r (.regular .W64 .W64 .ret) pc 1
        continue
    let some i := input.instructions.find? (·.pc == pc) | throw s!"PC outside decoded functions: {pc}"
    let [.instr op] ← Kraken.X64.Parser.parse i.asm | throw s!"not one instruction at {pc}: {i.asm}"
    r := {r with pcs := r.pcs.push pc}
    r ← interpret seed r op pc i.size
  throw "instruction budget exhausted"

def probe (input : ProbeInput) (actualServices : Bool := false) : Except String Json := do
  let w ← replayPrefix input.trace input.operation
  let some dev := w.k.wg | throw "no device after prefix"
  unless dev.indexTable.length == 1 do throw "expected one entry after recorded prefix"
  let before := dev.indexTable
  let (answer, after) ← (Leanux.WG.indexLookup [.handshake] input.query).run w
    |>.mapError Leanux.Stop.message
  let some afterDev := after.k.wg | throw "mirror lost device"
  let memory ← materializePeers dev input.offsets (← materialize before input.offsets input.preempt)
  let memory := put memory Binary.Layouts.keypairCounterAddress.toNat 8 w.k.keypairCounter
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
    | some e => do
      unless before.contains e do throw "returned entry is not in initial table"
      entryAddr e input.offsets
  unless r.state.data.regs.rax.toNat == answerAddr && r.state.data.regs.rsp.toNat == stackAddr + 8 do
    throw "return or stack mismatch"
  for reg in [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15] do
    unless r.state.data.regs.get64 reg == initial.data.regs.get64 reg do throw s!"callee-save mismatch: {repr reg}"
  let stackBase := BitVec.ofNat 64 (stackAddr - 0x800)
  let some stackBytes := memory.loadBytes stackBase 0x810 | throw "initial stack missing"
  let expected ← materializePeers afterDev input.offsets (← materialize afterDev.indexTable input.offsets input.preempt)
  let expected := match answer with
    | none => expected
    | some e => put expected outputAddr 8 (0x600000 + e.peer * 0x1000)
  let expected := put expected Binary.Layouts.keypairCounterAddress.toNat 8 after.k.keypairCounter
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
  -- Test-only decision projection; outcomes come from actual machine
  -- successors. This is not used by the theorem.
  let mut decisions : Array String := #[]
  let mut found := false
  for i in [:r.pcs.size] do
    let pc := r.pcs[i]!
    let next := r.pcs[i+1]?.getD stopAddr
    if pc == entry.pc + 0x32 then
      decisions := decisions.push s!"wg_index_hashtable_lookup.entry={if next == entry.pc + 0x34 then 1 else 0}"
    if pc == entry.pc + 0x5c then
      decisions := decisions.push s!"wg_index_hashtable_lookup.index_matches={if next == entry.pc + 0x95 then 1 else 0}"
    if pc == entry.pc + 0x6a then
      decisions := decisions.push s!"wg_index_hashtable_lookup.entry={if next == entry.pc + 0x34 then 1 else 0}"
    if pc == entry.pc + 0xab then
      decisions := decisions.push s!"wg_index_hashtable_lookup.type_matches={if next == entry.pc + 0xad then 1 else 0}"
    if pc == entry.pc + 0xb2 then
      found := true
      decisions := decisions.push "wg_index_hashtable_lookup.found=1"
    if pc == entry.pc + 0x71 && !found then
      decisions := decisions.push "wg_index_hashtable_lookup.found=0"
    if pc == entry.pc + 0xc3 then
      decisions := decisions.push s!"wg_index_hashtable_lookup.peer_alive={if next == entry.pc + 0xc5 then 1 else 0}"
    let helper := 0xffffffff81399610
    if pc == helper + 0x15 then
      decisions := decisions.push s!"wg_peer_get_maybe_zero.null={if next == helper + 0xdd then 1 else 0}"
    if pc == helper + 0x3d then
      decisions := decisions.push s!"__refcount_add_not_zero.old_zero={if next == helper + 0xb0 then 1 else 0}"
    if pc == helper + 0x63 then
      decisions := decisions.push s!"__refcount_add_not_zero.cmpxchg_failed={if next == helper + 0xf2 then 1 else 0}"
    if pc == helper + 0x79 then
      decisions := decisions.push s!"__refcount_add_not_zero.old_negative={if next == helper + 0xe1 then 1 else 0}"
    if pc == helper + 0x8d then
      decisions := decisions.push s!"__refcount_add_not_zero.wraps={if next == helper + 0xe1 then 1 else 0}"
    if pc == helper + 0x9d then
      decisions := decisions.push "wg_peer_get_maybe_zero.refcount_zero=0"
  -- Exercise the proof-side observer on every concrete instruction state.
  -- This checks its event ordering, not the unfinished physical relation R.
  let observed ← Binary.LookupObservation.observe w.netRxSection r.history.toList
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
  let some dev := w.k.wg | throw "no device"
  let [e] := dev.indexTable | throw "requires the single-entry fixture"
  let e := if keypairCase then {e with kind := .keypair, keypair := some 0} else e
  let dev := if keypairCase then
      {dev with
        indexTable := [e]
        keypairs := dev.keypairs.insert 0 {peer := e.peer}}
    else dev
  let some peer := dev.peers.get? e.peer | throw "missing peer"
  let w := { w with k := { w.k with wg := some { dev with
    peers := dev.peers.insert e.peer {peer with refcount := 0} } }, steps := #[] }
  let (answer1, after1) ← (Leanux.WG.indexLookup [e.kind] e.index).run w
    |>.mapError Leanux.Stop.message
  let (answer2, after2) ← (Leanux.WG.indexLookup [e.kind] e.index).run {after1 with steps := #[]}
    |>.mapError Leanux.Stop.message
  unless answer1.isNone && answer2.isNone && after1.k == w.k && after2.k == w.k do
    throw "dead-peer mirror behavior changed"
  let memory ← materialize dev.indexTable input.offsets input.preempt
  let memory ← materializePeers dev input.offsets memory
  let peerAddress := 0x600000 + e.peer * 0x1000
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
  -- The helper's TEST/JZ is at 0xffffffff81399622/25. Its two
  -- successors identify null/non-null without using the mirror's answer.
  let nullBranch := 0xffffffff81399625
  let outcome (r : Run) : Except String Bool := do
    let some i := r.pcs.toList.idxOf? nullBranch | throw "helper null check missing"
    let some successor := r.pcs[i+1]? | throw "helper successor missing"
    if successor == 0xffffffff813996ed then return true
    if successor == 0xffffffff8139962b then return false
    throw "unexpected helper null-check successor"
  let firstNull ← outcome r1
  let secondNull ← outcome r2
  unless !firstNull && secondNull do throw "expected changed null-peer decision on repeated lookup"
  let labels1 := after1.steps.map Leanux.Step.label
  let labels2 := after2.steps.map Leanux.Step.label
  unless labels1 == labels2 do throw "mirror's repeated decisions unexpectedly differ"
  let alias ← if keypairCase then do
      let some d := after2.k.wg | throw "device disappeared"
      let some k := d.keypairs.get? 0 | throw "keypair disappeared"
      unless k.peer == e.peer do throw "keypair peer alias changed"
      pure (Json.mkObj [("physical_entry_peer", toJson (0 : Nat)),
        ("mirror_keypair_peer", toJson k.peer), ("mirror_peer_address", toJson peerAddress)])
    else pure Json.null
  return Json.mkObj [
    ("status", toJson "counterexample reproduced"),
    ("scope", toJson "synthetic accepted mirror state; kernel reachability not established"),
    ("machine_null_peer_decisions", toJson [firstNull, secondNull]),
    ("mirror_first", toJson labels1), ("mirror_second", toJson labels2),
    ("machine_instructions", toJson [r1.pcs.size, r2.pcs.size]),
    ("machine_peer_pointer_before", toJson peerAddress),
    ("machine_peer_pointer_after", toJson (0 : Nat)),
    ("mirror_peer_id_after", toJson e.peer), ("keypair_alias", alias)]

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
  for (kind, address) in [(KcovKind.pc, 0xffffffff810f3100),
      (.cmp4, 0xffffffff810f3e80), (.constCmp4, 0xffffffff810f3f00),
      (.constCmp1, 0xffffffff810f3ec0)] do
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

def main (args : List String) : IO UInt32 := do
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
