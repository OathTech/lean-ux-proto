import PairAllowedipsState
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
  m := put m (names.table+AllowedipsMutationLayout.seq) 8 d.peerAllowedips.seq
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
    unless next.site == 70+site && next.bytes.length == 40 && next.bytes.drop 1 == List.replicate 39 0 &&
        (next.bytes.headD 2 == 0 || next.bytes.headD 2 == 1) do throw "service.allocation-record-shape"
    records := rest
    if next.bytes.headD 0 == 1 then
      let a := released.headD (AllowedipsProbe.nodeAddr names.nextNode)
      unless released.isEmpty do released := released.drop 1
      unless 0 < a && a%8 == 0 && a+input.lookup.offsets.nodeSize < 2^64 do throw "service.allocation-address"
      for i in [:input.lookup.offsets.nodeSize] do
        unless (m.get? (.ofNat 64 (a+i))).isNone do throw "service.allocation-not-fresh"
      m := m.storeBytes (.ofNat 64 a) (List.replicate input.lookup.offsets.nodeSize 0)
      names := {names with
        nextNode := names.nextNode+1,
        trie := {names.trie with nodes := names.trie.nodes++[(names.nextNode,a)]}}
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

def invoke (input : Input) (seed : UInt64) (s : Session)
    (family key cidr pid : Nat) (records : List HiddenRecord) : Except String (Session × Json) := do
  let width := if family == 4 then 32 else 128
  unless (family == 4 || family == 6) && key < 2^width && cidr < 256 do throw "insert.argument-width"
  assertAt s.names input.lookup.offsets s.binary.state.data.dmem s.world
  let peer ← Trie.address s.names.trie.peers (some pid)
  let mut memory := put s.binary.state.data.dmem stackAddr 8 stopAddr
  let network := (List.range (width/8)).map fun i => UInt8.ofNat (key / 256^(width/8-1-i) % 256)
  memory := memory.storeBytes (.ofNat 64 AllowedipsProbe.keyAddr) network
  let initial : MachineState := ⟨{dmem := memory,regs := {
    rdi := .ofNat s.names.table,rsi := .ofNat AllowedipsProbe.keyAddr,rdx := .ofNat cidr,
    rcx := .ofNat peer,rsp := .ofNat stackAddr,rbx := 17,rbp := 34,r12 := 51,r13 := 68,r14 := 85,r15 := 102}},
    .ofNat (if family == 4 then input.insert4 else input.insert6)⟩
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
      (some r) stopAddr (some #[])
      (some fun t => match TrustBase.KcovPlan .pc t with
        | none => .error "insert.coverage-inputs"
        | some writes => .ok (!writes.isEmpty))
    if r.state.pc.toBitVec.toNat == stopAddr then break
    let pc := r.state.pc.toBitVec.toNat
    let ra ← readNat r.state r.state.data.regs.rsp.toNat 8
    let (after,next,freed,rest) ← suppliedService input r names released remaining
    r := after; names := next; released := freed; remaining := rest
    services := services.push (pc,ra)
  unless r.state.pc.toBitVec.toNat == stopAddr do throw "insert.service-budget"
  unless remaining.isEmpty do throw "insert.unconsumed-allocation-record"
  let ambient := {s.world.ambient with
    hidden := some records, allocArmed := ["allocNode190","allocNode205","allocNode234"]}
  let w := {s.world with ambient}
  let (answer,world) ← (liftWG (insert family key cidr pid)).run w |>.mapError Stop.message
  unless world.hidden == some [] do throw "insert.mirror-input-cursor"
  unless r.state.data.regs.rax.toNat % 2^32 == (answer % (2^32 : Int)).toNat do throw "insert.result"
  unless r.state.data.regs.rsp == initial.data.regs.rsp+8 do throw "insert.return-stack"
  for reg in [Reg64.rbx,.rbp,.r12,.r13,.r14,.r15] do
    unless r.state.data.regs.get64 reg == initial.data.regs.get64 reg do throw "insert.callee-save"
  unless (← readNat r.state input.lookup.preempt 4) == input.lookup.entryPreempt do throw "insert.preempt"
  unless (← readNat r.state TrustBase.softirqPendingAddress.toNat 2) ==
      (← readNat initial TrustBase.softirqPendingAddress.toNat 2) do throw "insert.pending"
  unless (← readNat r.state coverageAddr 8) == r.coverage.size do throw "insert.coverage-count"
  for i in [:r.coverage.size] do
    unless (← readNat r.state (coverageAddr+8*(i+1)) 8) == r.coverage[i]! do throw "insert.coverage-word"
  assertAt names input.lookup.offsets r.state.data.dmem world
  return (⟨names,world,r,released⟩,Json.mkObj [("family",toJson family),("cidr",toJson cidr),
    ("result",toJson answer),("instructions",toJson r.pcs.size),("services",toJson services),
    ("decisions",toJson ((world.steps.toList.drop s.world.steps.size).map Step.label))])

def lookup (input : Input) (seed : UInt64) (s : Session) (family key : Nat) : Except String (Session × Json) := do
  let some d := s.world.wg.dev | throw "lookup.device"
  assertAt s.names input.lookup.offsets s.binary.state.data.dmem s.world
  let width := if family == 4 then 32 else 128
  let root := if family == 4 then d.peerAllowedips.root4 else d.peerAllowedips.root6
  let network := (List.range (width/8)).map fun i => UInt8.ofNat (key / 256^(width/8-1-i) % 256)
  let memory := (put s.binary.state.data.dmem stackAddr 8 stopAddr).storeBytes
    (.ofNat 64 AllowedipsProbe.keyAddr) network
  let (world,binary,report) ← Trie.lookup s.names.trie input.lookup seed memory s.binary.coverage s.world root width key
  assertAt s.names input.lookup.offsets binary.state.data.dmem world
  return ({s with world,binary},report)

end Binary.Pair.Allowedips
