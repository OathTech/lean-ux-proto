import PairAllowedipsLookupCheck
import PairAllowedipsPlacement
import PairAllowedipsExact
import PairAllowedipsRoot
import PairAllowedipsRootBoundary
import PairAllowedipsReturn
import PairAllowedipsNodeInit
import PairAllowedipsNames
import PairAllowedips

namespace Binary.Pair.Allowedips
open Lean Leanux Leanux.WG

structure Input where
  lookup : AllowedipsProbe.Input
  insert4 : Nat
  insert6 : Nat
  add : Nat
  alloc : Nat
  free : Nat
  allocationReturns : Array (Nat × Nat)
  freeReturn : Nat
  cacheWord : Nat
  deriving FromJson

structure Session where
  names : Names
  world : World
  binary : Run
  released : List Nat := []

def cacheAddress : Nat := 0xc00000

/-- Initially empty, labelled constructed state. No later invocation uses this
materializer: caller ABI bytes and explicit generic service effects are the
only supplied writes. -/
def fixture (input : Input) (w : World) : Except String Session := do
  let some d := w.wg.dev | throw "fixture.device"
  unless d.nodes.isEmpty && d.peerAllowedips.root4.isNone && d.peerAllowedips.root6.isNone do
    throw "fixture.requires-empty-table"
  let names : Names := ⟨tableAddr,⟨[],d.peers.toList.map (fun (id,_) => (id,peerAddr id))⟩,d.nextNode⟩
  let mut m ← AllowedipsProbe.materialize d input.lookup.offsets 0 128 input.lookup.preempt input.lookup.entryPreempt
  m := m.storeBytes (.ofNat 64 names.table) (List.replicate AllowedipsMutationLayout.tableSize 0)
  m := put m (names.table+AllowedipsMutationLayout.seq) 8 d.peerAllowedips.seq.toNat
  m := put m input.cacheWord 8 cacheAddress
  for (id,a) in names.trie.peers do
    let some p := d.peers.get? id | throw "fixture.peer"
    unless p.allowedipsList.isEmpty do throw "fixture.requires-empty-peer-list"
    m := m.storeBytes (.ofNat 64 a) (List.replicate Layouts.peerSize 0)
    m := put m (a+input.lookup.offsets.peerRefcount) 4 p.refcount
    let head := a+AllowedipsMutationLayout.allowedips_list
    m := put (put m head 8 head) (head+8) 8 head
  assertAt names input.lookup.offsets m w
  return ⟨names,w,{state := ⟨{dmem := m},0⟩},[]⟩

def record (site : Nat) (success : Bool) : HiddenRecord :=
  ⟨70+site,(if success then 1 else 0)::List.replicate 39 0⟩

/-- One explicit generic allocator interface return. No WireGuard instruction
is skipped. Allocation creates zero bytes, a fresh identity and ABI return;
release removes the owned bytes so use after release fails during execution. -/
def suppliedService (input : Input) (r : Run) (names : Names) (released : List Nat)
    (records : List HiddenRecord) : Except String (Run × Names × List Nat × List HiddenRecord) := do
  let pc := r.state.pc.toBitVec.toNat
  let ra ← readNat r.state r.state.data.regs.rsp.toNat 8
  unless r.state.data.regs.rdi.toNat == cacheAddress do throw "service.cache"
  let mut m := r.state.data.dmem
  let mut names := names
  let mut released := released
  let mut records := records
  let mut answer := 0
  if pc == input.alloc then
    unless r.state.data.regs.rsi.toNat == 0xdc0 do throw "service.allocation-flags"
    let some (_,site) := input.allocationReturns.find? (·.1 == ra) | throw "service.allocation-return-site"
    let next::rest := records | throw "service.allocation-record-missing"
    unless next.site == 70+site && next.bytes.length == 40 &&
        (next.bytes.headD 2 == 0 || next.bytes.headD 2 == 1) do throw "service.allocation-record-shape"
    records := rest
    if next.bytes.headD 0 == 1 then
      let a := released.headD (AllowedipsProbe.nodeAddr names.nextNode)
      unless released.isEmpty do released := released.drop 1
      unless 0 < a && a%8 == 0 && a+input.lookup.offsets.nodeSize < 2^64 do throw "service.allocation-address"
      for i in [:input.lookup.offsets.nodeSize] do
        unless (m.get? (.ofNat 64 (a+i))).isNone do throw "service.allocation-not-fresh"
      m := m.storeBytes (.ofNat 64 a) (List.replicate input.lookup.offsets.nodeSize 0)
      names := names.allocated a
      answer := a
  else if pc == input.free then
    unless ra == input.freeReturn do throw "service.free-return-site"
    let a := r.state.data.regs.rsi.toNat
    unless names.trie.nodes.any (·.2 == a) do throw "service.free-unowned"
    names := {names with trie := {names.trie with nodes := names.trie.nodes.filter (·.2 != a)}}
    for i in [:input.lookup.offsets.nodeSize] do m := m.erase (.ofNat 64 (a+i))
    released := released++[a]
  else throw "service.unknown-entry"
  let state : MachineState := ⟨{r.state.data with dmem := m,regs := {
    r.state.data.regs with rax := .ofNat answer,rsp := r.state.data.regs.rsp+8}},.ofNat ra⟩
  return ({r with state},names,released,records)

def invokeFrom (input : Input) (seed : UInt64) (s : Session)
    (family key cidr pid : Nat) (records : List HiddenRecord)
    (initial : MachineState) (frame : CallFrame)
    (service : Run → Names → List Nat → List HiddenRecord →
      Except String (Run × Names × List Nat × List HiddenRecord)) : Except String (Session × Json) := do
  let width := if family == 4 then 32 else 128
  unless (family == 4 || family == 6) && key < 2^width && cidr < 256 do throw "insert.argument-width"
  assertAt s.names input.lookup.offsets initial.data.dmem s.world
  let peer ← Trie.address s.names.trie.peers (some pid)
  unless initial.pc.toBitVec.toNat == (if family == 4 then input.insert4 else input.insert6) &&
      initial.data.regs.rdi.toNat == s.names.table && initial.data.regs.rcx.toNat == peer &&
      initial.data.regs.rdx.toNat % 256 == cidr && initial.data.regs.rsp.toNat == frame.stack do
    throw "insert.entry-abi"
  unless (← readNat initial frame.stack 8) == frame.returnPC do throw "insert.entry-return-word"
  let some bytes := initial.data.dmem.loadBytes initial.data.regs.rsi.toBitVec (width/8)
    | throw "insert.query-unmapped"
  unless bytes.foldl (fun a b => a*256+b.toNat) 0 == key do throw "insert.query-value"
  let mut r := {s.binary with state := initial,pcs := #[],reads := #[],writes := #[],history := #[]}
  let mut names := s.names
  let mut released := s.released
  let mut remaining := records
  let mut services := #[]
  -- add has at most two allocations and one rollback release; the budget
  -- refuses unexpected extra service calls rather than synthesizing outcomes.
  for _ in [:4] do
    r ← runUntil input.lookup.instructions input.lookup.labels input.lookup.hooks input.lookup.preempt
      r.state seed true input.lookup.budget input.lookup.entryPreempt #[input.alloc,input.free]
      (some r) frame.returnPC (some #[input.add+0xf7,input.add+0x9c,input.add+0x120,input.add+0x3ca,input.add+0x3e5,input.add+0x443,input.add+0x156,input.add+0x1ff,input.add+0x549,input.add+0x54e,input.insert4+0x42,input.insert6+0x4f])
      (some fun t => match TrustBase.KcovPlan .pc t with
        | none => .error "insert.coverage-inputs"
        | some writes => .ok (!writes.isEmpty))
    if r.state.pc.toBitVec.toNat == frame.returnPC then break
    let pc := r.state.pc.toBitVec.toNat
    let ra ← readNat r.state r.state.data.regs.rsp.toNat 8
    let (after,next,freed,rest) ← service r names released remaining
    r := after; names := next; released := freed; remaining := rest
    services := services.push (pc,ra)
  unless r.state.pc.toBitVec.toNat == frame.returnPC do throw "insert.service-budget"
  let context ← Common.readContext initial.data.dmem
  let placementHistory := r.history.filter fun t =>
    [input.add+0xf7,input.add+0x9c,input.add+0x120,input.add+0x3ca].contains t.pc.toBitVec.toNat
  let visits ← Placement.check s.names input.lookup.offsets context input.add s.world family key cidr pid frame.stack placementHistory
  let returnSegments ← Return.check r.history r.state
  unless returnSegments==2 do throw "insert.return-segment-count"
  let exactSegments ← Exact.check r.history
  let nodeInitSegments ← NodeInit.check r.history
  let rootSegments ← Root.check r.history
  let rootBoundaries ← Root.checkBoundary s.names input.lookup.offsets s.world key cidr pid r.history
  unless rootBoundaries==rootSegments do throw "insert.root-boundary-count"
  let ambient := {s.world.ambient with
    hidden := some records, allocArmed := ["allocNode190","allocNode205","allocNode234"]}
  let w := {s.world with ambient}
  let (answer,world) ← (liftWG (insert family key cidr pid)).run w |>.mapError Stop.message
  let expectedExact := (world.steps.toList.drop s.world.steps.size).countP fun step =>
    step.decision==.addExact && step.outcome
  unless exactSegments==expectedExact do throw "insert.exact-segment-count"
  let expectedNodeInit := (world.steps.toList.drop s.world.steps.size).countP fun step =>
    step.decision==.addNewnodeNoMem && !step.outcome
  unless nodeInitSegments==expectedNodeInit do throw "insert.node-init-segment-count"
  let expectedRoot := if answer==0 && (world.steps.toList.drop s.world.steps.size).any
      (fun step => step.decision==.addEmptyTrie && step.outcome) then 1 else 0
  unless rootSegments==expectedRoot do throw "insert.root-segment-count"
  unless world.hidden == some remaining do throw "insert.mirror-input-cursor"
  unless r.state.data.regs.rax.toNat % 2^32 == (answer % (2^32 : Int)).toNat do throw "insert.result"
  unless r.state.data.regs.rsp == initial.data.regs.rsp+8 do throw "insert.return-stack"
  for reg in [Reg64.rbx,.rbp,.r12,.r13,.r14,.r15] do
    unless r.state.data.regs.get64 reg == initial.data.regs.get64 reg do throw "insert.callee-save"
  unless (← readNat r.state input.lookup.preempt 4) == input.lookup.entryPreempt do throw "insert.preempt"
  unless (← readNat r.state TrustBase.softirqPendingAddress.toNat 2) ==
      (← readNat initial TrustBase.softirqPendingAddress.toNat 2) do throw "insert.pending"
  unless (← readNat r.state frame.coverage 8) == r.coverage.size do throw "insert.coverage-count"
  for i in [:r.coverage.size] do
    unless (← readNat r.state (frame.coverage+8*(i+1)) 8) == r.coverage[i]! do throw "insert.coverage-word"
  assertAt names input.lookup.offsets r.state.data.dmem world
  return (⟨names,world,r,released⟩,Json.mkObj [("family",toJson family),("cidr",toJson cidr),
    ("result",toJson answer),("placementVisits",toJson visits),("exactSegments",toJson exactSegments),
    ("nodeInitSegments",toJson nodeInitSegments),("rootSegments",toJson rootSegments),("returnSegments",toJson returnSegments),("instructions",toJson r.pcs.size),("services",toJson services),
    ("coverage",toJson (r.coverage.toList.drop s.binary.coverage.size)),
    ("comparisons",toJson (r.comparisons.toList.drop s.binary.comparisons.size)),
    ("decisions",toJson ((world.steps.toList.drop s.world.steps.size).map Step.label))])

def invoke (input : Input) (seed : UInt64) (s : Session)
    (family key cidr pid : Nat) (records : List HiddenRecord) : Except String (Session × Json) := do
  let width := if family == 4 then 32 else 128
  let peer ← Trie.address s.names.trie.peers (some pid)
  let mut memory := put s.binary.state.data.dmem stackAddr 8 stopAddr
  let network := (List.range (width/8)).map fun i => UInt8.ofNat (key / 256^(width/8-1-i) % 256)
  memory := memory.storeBytes (.ofNat 64 AllowedipsProbe.keyAddr) network
  let initial : MachineState := ⟨{dmem := memory,regs := {
    rdi := .ofNat s.names.table,rsi := .ofNat AllowedipsProbe.keyAddr,rdx := .ofNat cidr,
    rcx := .ofNat peer,rsp := .ofNat stackAddr,rbx := 17,rbp := 34,r12 := 51,r13 := 68,r14 := 85,r15 := 102}},
    .ofNat (if family == 4 then input.insert4 else input.insert6)⟩
  invokeFrom input seed s family key cidr pid records initial {} (suppliedService input)

def lookup (input : Input) (seed : UInt64) (s : Session) (family key : Nat) : Except String (Session × Json) := do
  let some d := s.world.wg.dev | throw "lookup.device"
  assertAt s.names input.lookup.offsets s.binary.state.data.dmem s.world
  let width := if family == 4 then 32 else 128
  let root := if family == 4 then d.peerAllowedips.root4 else d.peerAllowedips.root6
  let network := (List.range (width/8)).map fun i => UInt8.ofNat (key / 256^(width/8-1-i) % 256)
  let memory := (put s.binary.state.data.dmem stackAddr 8 stopAddr).storeBytes
    (.ofNat 64 AllowedipsProbe.keyAddr) network
  let regs : Reg64s := {
    rdi := .ofNat (← Trie.address s.names.trie.nodes root),rsi := .ofNat width,
    rdx := .ofNat AllowedipsProbe.keyAddr,rsp := .ofNat stackAddr,
    rbx := 0x11,rbp := 0x22,r12 := 0x33,r13 := 0x44,r14 := 0x55,r15 := 0x66}
  let initial : MachineState := ⟨{regs,dmem := memory},.ofNat input.lookup.entry⟩
  let context := Trie.fixtureLoopContext input.lookup
  lookupBoundary s.names input.lookup ⟨context.coverage,.ofNat 32 input.lookup.entryPreempt⟩
    initial s.world family key (.ofNat stopAddr)
  let (world,binary,report) ← Trie.lookupFrom s.names.trie input.lookup seed initial {} context
    s.binary.coverage s.world root width key
  assertAt s.names input.lookup.offsets binary.state.data.dmem world
  return ({s with world,binary},report)

end Binary.Pair.Allowedips
