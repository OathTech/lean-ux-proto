import PairCapture
import PairSequenceRunner

namespace Binary.Pair.MutatorCapture
open Lean Leanux Leanux.WG

structure Snapshot extends Capture.Snapshot where
  anchor : String
  deriving FromJson

/-- Identity only: public keys label peer allocations; allocation counters
label keypairs. Values of the index projection are not taken from this prefix. -/
def names (input : ProbeInput) (snapshot : Snapshot) (layout : Json)
    (initial : MachineState) (d : Device) : Except String Names := do
  let keyOffset := (← Capture.member layout "wg_peer" "handshake") +
    (← Capture.member layout "noise_handshake" "remote_static")
  let keypairId := ← Capture.member layout "noise_keypair" "internal_id"
  let mut peers := []
  for (id,peer) in d.peers.toList do
    let candidates := snapshot.initial.peers.filter (fun p => p.publicKey.toList==peer.remoteStatic.map UInt8.toNat)
    let [candidate] := candidates.toList | throw "capture.peer-identity-not-unique"
    let some key := initial.data.dmem.loadBytes (.ofNat 64 (candidate.address+keyOffset)) 32
      | throw "capture.peer-key-unmapped"
    unless key.map UInt8.toNat==candidate.publicKey.toList do throw "capture.peer-key-metadata"
    peers := peers++[(id,candidate.address)]
  unless peers.length==snapshot.initial.peers.size do throw "capture.uninterpreted-peer"
  let mut owners := peers.map fun (id,a) => (IndexOwner.handshake id,a+input.offsets.peerHandshake+input.offsets.handshakeEntry)
  for (id,keypair) in d.keypairs.toList do
    let mut candidates := []
    for address in snapshot.initial.keypairs do
      if (← readNat initial (address+keypairId) 8)==keypair.internalId then candidates := address::candidates
    let [address] := candidates | throw "capture.keypair-allocation-id-not-unique"
    owners := owners++[(IndexOwner.keypair id,address+input.offsets.keypairEntry)]
  unless d.keypairs.size==snapshot.initial.keypairs.size do throw "capture.uninterpreted-keypair"
  let n : Names := ⟨initial.data.regs.rdi.toNat,peers,owners⟩
  n.validate input.offsets |>.mapError DecodeError.message
  unless (← readNat initial (snapshot.initial.device+Layouts.device_index_hashtable) 8)==n.table do
    throw "capture.device-table"
  return n

/-- Reify the independently decoded physical projection as a source call
input. Unobserved World/environment fields are supplied by the recorded
prefix. This does not assert that prefix is the compiled caller's entry. -/
def sourceWorld (template : World) (view : LookupState) : Except String World := do
  let some original := template.k.wg | throw "capture.source-device"
  let mut d := {original with indexTable := view.buckets.toList.flatten}
  for (owner,value) in view.ownerWords do
    match owner with
    | .handshake id =>
      let some peer := d.peers[id]? | throw "capture.source-peer-owner"
      d := {d with peers := d.peers.insert id {peer with handshakeEntryPeer := value}}
    | .keypair id =>
      let some keypair := d.keypairs[id]? | throw "capture.source-keypair-owner"
      d := {d with keypairs := d.keypairs.insert id {keypair with peer := value}}
  for (id,value) in view.refcounts do
    let some peer := d.peers[id]? | throw "capture.source-count-owner"
    d := {d with peers := d.peers.insert id {peer with refcount := value}}
  return {template with k := {template.k with wg := some d}}

def call (snapshot : Snapshot) (n : Names) (initial : MachineState) : Except String Sequence.Call := do
  let owner ← (ownerAt n "capture.old-argument" initial.data.regs.rsi.toNat).mapError DecodeError.message
  match snapshot.anchor with
  | "remove" => return .remove owner
  | "replace" =>
    let .handshake pid := owner | throw "capture.replace.old-kind"
    let new ← (ownerAt n "capture.new-argument" initial.data.regs.rdx.toNat).mapError DecodeError.message
    let .keypair kid := new | throw "capture.replace.new-kind"
    return .replace pid kid
  | _ => throw "capture.unknown-mutator"

def rejected (label : String) (test : Except String α) : Except String Json :=
  match test with
  | .ok _ => .error s!"control accepted: {label}"
  | .error message => .ok (Json.mkObj [("control",toJson label),("rejected",toJson message)])

/-- Small mutations of the actual entry exercise identity and ownership
checks. They do not replace or modify the successful replay's input. -/
def entryControls (input : ProbeInput) (snapshot : Snapshot) (layout : Json)
    (initial : MachineState) (n : Names) (d : Device) (world : World) : Except String (Array Json) := do
  let missing := {snapshot with initial := {snapshot.initial with peers := #[]}}
  let identity ← rejected "missing allocation identity" (names input missing layout initial d)
  let a := initial.data.regs.rsi.toNat+input.offsets.hash+input.offsets.pprev
  unless (← readNat initial a 8) != 0 do throw "control requires the selected linked entry"
  let unlinked := put initial.data.dmem a 8 0
  let ownership ← rejected "linked owner with NULL pprev" (Remove.assertAt n input.offsets unlinked world)
  return #[identity,ownership]

def returnControls (snapshot : Snapshot) (actual : Run) : Except String (Array Json) := do
  let history ← rejected "missing executed PCs"
    (Capture.compareReturn {snapshot.toSnapshot with executedPCs := #[]} actual)
  -- A one-byte endpoint keeps the negative control cheap while exercising
  -- the same comparator used on every byte of the independent full capture.
  let address := actual.state.data.regs.rsp.toNat-8
  let value ← readNat actual.state address 1
  let endpoint : Capture.Endpoint := {
    registers := snapshot.returned.registers
    blocks := #[⟨address,#[(value+1)%256]⟩] }
  let memory ← rejected "changed captured return byte" (Capture.compareEndpoint endpoint actual.state)
  return #[history,memory]

def run (input : ProbeInput) (snapshot : Snapshot) (layout : Json) : Except String Json := do
  unless snapshot.executionMode=="sequential" &&
      snapshot.completedOperations.toList==List.range snapshot.operation &&
      (← input.trace.getObjValAs? String "id")==snapshot.trace do throw "capture.workload-or-mode"
  let template ← replayRecordedPrefix input.trace input.operation
  let some d := template.k.wg | throw "capture.identity-prefix-device"
  let initial ← snapshot.initial.registers.state (← Capture.loadMemory snapshot.initial.blocks)
  let n ← names input snapshot layout initial d
  let view ← (reconstruct n input.offsets initial.data.dmem).mapError DecodeError.message
  let prefixMatch := match compareState view (target d) with | .ok _ => "equal" | .error e => e
  let world ← sourceWorld template view
  Remove.assertAt n input.offsets initial.data.dmem world
  let controls ← entryControls input snapshot layout initial n d world
  let op ← call snapshot n initial
  let frame ← Capture.callFrame input snapshot.toSnapshot layout initial
  let c ← Index.readContext initial.data.dmem
  match op with
  | .remove owner => Remove.callBoundary n input.offsets c initial world owner (.ofNat frame.returnPC)
  | .replace pid kid => Replace.callBoundary n input.offsets c initial world pid kid (.ofNat frame.returnPC)
  | .lookup _ _ => throw "capture.mutator-was-lookup"
  let (answer,finalWorld) ← (Sequence.source op).run world |>.mapError Stop.message
  let mut coverage := #[]
  for i in [:snapshot.initial.coverageUsed] do
    coverage := coverage.push (← readNat initial (frame.coverage+8*(i+1)) 8)
  let mut outcomes := #[]
  for seed in [(0 : UInt64),0xffffffffffffffff] do
    let prior : Run := {state := initial,coverage,history := #[initial]}
    let actual ← runUntil input.instructions input.labels input.hooks input.preempt initial seed true
      frame.budget frame.entryPreempt #[] (some prior) frame.returnPC (some #[])
      (some fun s => match TrustBase.KcovPlan .pc s with
        | none => .error "capture.coverage-inputs"
        | some writes => .ok (!writes.isEmpty))
    Sequence.resultCheck n initial actual.state answer
    Remove.assertAt n input.offsets actual.state.data.dmem finalWorld
    Remove.assertAt n input.offsets (← Capture.loadMemory snapshot.returned.blocks) finalWorld
    unless Trie.coverageCheck c actual.state.data.dmem &&
        Trie.coverageDataCheck ⟨c.coverage,c.preempt+512⟩ actual.state.data.dmem do throw "capture.return-readiness"
    let checked ← Capture.compareReturn snapshot.toSnapshot actual
    let returnChecks ← returnControls snapshot actual
    outcomes := outcomes.push (Json.mkObj [("seed",toJson seed.toNat),("instructions",toJson actual.pcs.size),
      ("compared_bytes",toJson checked),("coverage_added",toJson (actual.coverage.size-coverage.size)),
      ("return_controls",toJson returnChecks)])
  return Json.mkObj [("status",toJson "pass"),("anchor",toJson snapshot.anchor),
    ("origin",toJson "actual kernel entry and return bytes; no relocation or heap materialization"),
    ("source_input",toJson "index projection reconstructed from captured entry; identities and unobserved fields supplied by recorded prefix"),
    ("identity_prefix_operation",toJson input.operation),("captured_operation",toJson snapshot.operation),
    ("prefix_projection_comparison",toJson prefixMatch),("call",toJson (reprStr op)),
    ("answer",toJson (reprStr answer)),("entry_preempt",toJson frame.entryPreempt),
    ("capacity",toJson snapshot.initial.capacity),("entry_controls",toJson controls),("runs",toJson outcomes)]

end Binary.Pair.MutatorCapture
