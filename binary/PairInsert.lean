import PairInsertInput
import IndexInsertImage

namespace Binary.Pair.Insert
open Lean Leanux Leanux.WG

def entry : Nat := IndexInsertImage.Insert.entry.toBitVec.toNat
def randomEntry : Nat := 0xffffffff81375000

/-- Present-state readiness; nested BH-disable requires a third coverage
phase. The random provider's private state is not fabricated by this check. -/
def callBoundary (n : Names) (o : Offsets) (c : CommonBitsCoverage.Context)
    (s : MachineState) (w : World) (owner : IndexOwner) (ra : UInt64) : Except String Unit := do
  Remove.assertAt n o s.data.dmem w
  let address ← addressOf n owner
  unless s.pc.toBitVec.toNat==entry && s.data.regs.rdi.toNat==n.table &&
      s.data.regs.rsi.toNat==address do throw "insert.call.entry-arguments"
  let kind ← (word s.data.dmem "insert.kind" (address+o.kind) 4).mapError DecodeError.message
  unless kind==(match owner with | .handshake _ => 1 | .keypair _ => 2) do
    throw "insert.call.kind"
  let _ ← (word s.data.dmem "insert.next" (address+o.hash+o.next) 8).mapError DecodeError.message
  let _ ← (word s.data.dmem "insert.index" (address+o.index) 4).mapError DecodeError.message
  Index.callFrameCheck n o c s ra 7
  unless Trie.coverageDataCheck ⟨c.coverage,c.preempt+1024⟩ s.data.dmem do
    throw "insert.call.nested-coverage"
  unless (c.preempt+1024) &&& 0x000f0000 == 0 do throw "insert.call.nested-hardirq"
  unless w.hidden.isSome do throw "insert.call.recorded-input-required"

/-- A supplied random-service return for generated tests. This transition is
explicitly NOT execution of get_random_u32 or its entropy/recording callees.
Its unchanged-memory/caller-save choice is one service-interface fixture.
Captured tests must supply the actual service state change separately. -/
def suppliedRandomReturn (r : Run) (value : Nat) : Except String Run := do
  unless r.state.pc.toBitVec.toNat==randomEntry && value<2^32 do
    throw "insert.random.boundary"
  let ra ← readNat r.state r.state.data.regs.rsp.toNat 8
  unless ra==entry+0x79 do throw "insert.random.return-address"
  let state : MachineState := ⟨{r.state.data with regs := {r.state.data.regs with
    rax := .ofNat value,rsp := r.state.data.regs.rsp+8}},.ofNat ra⟩
  return {r with state}

def invokeFrom (input : ProbeInput) (seed : UInt64) (s : Session) (owner : IndexOwner)
    (initial : MachineState) (frame : CallFrame)
    (randomReturn : Nat → Run → Nat → Except String Run)
    (serviceDescription : String)
    : Except String (Session × Json) := do
  let address ← addressOf s.names owner
  let context ← Index.readContext initial.data.dmem
  callBoundary s.names input.offsets context initial s.world owner (.ofNat frame.returnPC)
  let some records := s.world.hidden | throw "insert: missing recorded inputs"
  let some d := s.world.k.wg | throw "insert: missing device"
  let unlinked := {s.world with k := {s.world.k with wg := some {d with
    indexTable := d.indexTable.filter (fun e => !(e.owner==owner))}}}
  let mut remaining := records
  let mut draws := #[]
  let mut r := {s.binary with state := initial,history := #[initial],pcs := #[],reads := #[],writes := #[]}
  -- Each accepted call consumes at most the supplied record count. The
  -- extra iteration executes the successful draw's suffix through RET.
  for _ in [:records.length+1] do
    r ← runUntil input.instructions input.labels input.hooks input.preempt r.state seed true
      frame.budget context.preempt.toNat #[randomEntry] (some r) frame.returnPC (some #[])
      (some fun t => match TrustBase.KcovPlan .pc t with
        | none => .error "insert coverage callback inputs are missing"
        | some writes => .ok (!writes.isEmpty))
    if r.state.pc.toBitVec.toNat==frame.returnPC then break
    unless r.state.pc.toBitVec.toNat==randomEntry do throw "insert: unexpected boundary"
    Remove.assertAt s.names input.offsets r.state.data.dmem unlinked
    let (value,rest) ← draw remaining
    r ← randomReturn draws.size r value
    remaining := rest
    draws := draws.push value
  unless r.state.pc.toBitVec.toNat==frame.returnPC do throw "insert: input iteration budget exhausted"
  let (answer,world) ← indexInsert owner |>.run s.world |>.mapError Stop.message
  Remove.assertAt s.names input.offsets r.state.data.dmem world
  unless world.hidden==some remaining do throw "insert.return.input-cursor"
  unless r.state.data.regs.rax.toNat==answer && r.state.data.regs.rsp.toNat==initial.data.regs.rsp.toNat+8 do
    throw "insert.return.result-stack"
  for reg in [Reg64.rbx,.rbp,.r12,.r13,.r14,.r15] do
    unless r.state.data.regs.get64 reg==initial.data.regs.get64 reg do throw "insert.return.callee-save"
  unless (← readNat r.state input.preempt 4)==context.preempt.toNat do throw "insert.return.preempt"
  unless (← readNat r.state frame.pending 2)==(← readNat initial frame.pending 2) do throw "insert.return.pending"
  unless (← readNat r.state frame.coverage 8)==r.coverage.size do throw "insert.return.coverage-count"
  for i in [:r.coverage.size] do
    unless (← readNat r.state (frame.coverage+8*(i+1)) 8)==r.coverage[i]! do throw "insert.return.coverage-word"
  for (a,size) in r.writes do
    unless within a size (frame.stack-0x800) 0x800 || within a size frame.coverage frame.coverageSize ||
        within a size input.preempt 4 || within a size s.names.table input.offsets.tableSize ||
        s.names.owners.any (fun (_,base) => within a size (base+input.offsets.hash) 16) ||
        within a size (address+input.offsets.index) 4 do
      throw s!"insert write outside footprint: {a}/{size}"
  return ({s with world,binary := r,call := s.call+1},Json.mkObj [
    ("instructions",toJson r.pcs.size),("draws",toJson draws),("answer",toJson answer),
    ("random_service",toJson serviceDescription),
    ("coverage",toJson (r.coverage.toList.drop s.binary.coverage.size)),
    ("decisions",toJson ((world.steps.toList.drop s.world.steps.size).map Step.label))])

def invoke (input : ProbeInput) (seed : UInt64) (s : Session) (owner : IndexOwner)
    : Except String (Session × Json) := do
  let address ← addressOf s.names owner
  let memory := put s.binary.state.data.dmem stackAddr 8 stopAddr
  let initial : MachineState := ⟨{dmem := memory,regs := {
    rdi := .ofNat s.names.table,rsi := .ofNat address,rsp := .ofNat stackAddr,
    rbx := 17,rbp := 34,r12 := 51,r13 := 68,r14 := 85,r15 := 102}},.ofNat entry⟩
  invokeFrom input seed s owner initial {} (fun _ => suppliedRandomReturn)
    "supplied interface return; body not executed"

end Binary.Pair.Insert
