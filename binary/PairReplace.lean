import PairRemove

namespace Binary.Pair.Replace
open Lean Leanux Leanux.WG

def entry : Nat := 0xffffffff813a0350

/-- The caller supplies two existing embedded entries. Only successful
replacement requires the new entry to be unlinked, writable and a keypair.
Its peer word is independent of the handshake owner's peer word. -/
def callBoundary (n : Names) (o : Offsets) (c : CommonBitsCoverage.Context)
    (s : MachineState) (w : World) (pid : PeerId) (kid : KeypairId)
    (ra : UInt64) : Except String Unit := do
  Remove.assertAt n o s.data.dmem w
  let old ← addressOf n (.handshake pid)
  let new ← addressOf n (.keypair kid)
  unless s.pc.toBitVec.toNat==entry && s.data.regs.rsi.toNat==old &&
      s.data.regs.rdx.toNat==new do throw "replace.call.entry-arguments"
  let some d := w.k.wg | throw "replace.call.device"
  if d.indexTable.any (·.owner==.handshake pid) then
    if d.indexTable.any (·.owner==.keypair kid) then throw "replace.call.new-linked"
    let kind ← (word s.data.dmem "replace.new.kind" (new+o.kind) 4).mapError DecodeError.message
    unless kind==2 do throw "replace.call.new-kind"
    let _ ← (word s.data.dmem "replace.new.next" (new+o.hash+o.next) 8).mapError DecodeError.message
    let _ ← (word s.data.dmem "replace.new.index" (new+o.index) 4).mapError DecodeError.message
  Index.callFrameCheck n o c s ra 5

def fixture (input : ProbeInput) (w : World) : Except String Session := do
  let s ← Remove.fixture input w
  let mut m := s.binary.state.data.dmem
  let some d := w.k.wg | throw "replace fixture: no device"
  for (owner,a) in s.names.owners do
    unless d.indexTable.any (·.owner==owner) do
      let kind := match owner with | .handshake _ => 1 | .keypair _ => 2
      m := put (put m (a+input.offsets.kind) 4 kind) (a+input.offsets.index) 4 0
  return {s with binary := {s.binary with state := {s.binary.state with data := {s.binary.state.data with dmem := m}}}}

def invoke (input : ProbeInput) (seed : UInt64) (s : Session) (pid : PeerId)
    (kid : KeypairId) : Except String (Session × Json) := do
  let old ← addressOf s.names (.handshake pid)
  let new ← addressOf s.names (.keypair kid)
  let memory := put s.binary.state.data.dmem stackAddr 8 stopAddr
  let initial : MachineState := ⟨{dmem := memory,regs := {
    rdi := .ofNat s.names.table,rsi := .ofNat old,rdx := .ofNat new,rsp := .ofNat stackAddr,
    rbx := 17,rbp := 34,r12 := 51,r13 := 0xabc044,r14 := 85,r15 := 102}},.ofNat entry⟩
  let context ← Index.readContext memory
  callBoundary s.names input.offsets context initial s.world pid kid (.ofNat stopAddr)
  let prior := {s.binary with state := initial,history := #[initial],pcs := #[],reads := #[],writes := #[]}
  let r ← runUntil input.instructions input.labels input.hooks input.preempt initial seed true
    10000 0 #[] (some prior) stopAddr (some #[])
    (some fun t => match TrustBase.KcovPlan .pc t with
      | none => .error "replace coverage callback inputs are missing"
      | some writes => .ok (!writes.isEmpty))
  let (answer,world) ← (indexReplaceHandshake pid kid).run s.world |>.mapError Stop.message
  Remove.assertAt s.names input.offsets r.state.data.dmem world
  unless r.state.pc.toBitVec.toNat==stopAddr && r.state.data.regs.rsp.toNat==stackAddr+8 do
    throw "replace return: PC/stack"
  unless r.state.data.regs.rax.toNat%256==(if answer then 1 else 0) do
    throw "replace return: low-byte result"
  for reg in [Reg64.rbx,.rbp,.r12,.r13,.r14,.r15] do
    unless r.state.data.regs.get64 reg==initial.data.regs.get64 reg do throw "replace return: callee save"
  unless (← readNat r.state input.preempt 4)==0 do throw "replace return: preempt"
  unless (← readNat r.state 0xffffffff81cc85e0 2)==0 do throw "replace return: pending"
  unless (← readNat r.state coverageAddr 8)==r.coverage.size do throw "replace return: coverage count"
  for i in [:r.coverage.size] do
    unless (← readNat r.state (coverageAddr+8*(i+1)) 8)==r.coverage[i]! do throw "replace return: coverage word"
  for (address,size) in r.writes do
    unless within address size (stackAddr-0x800) 0x800 || within address size coverageAddr coverageBytes ||
        within address size input.preempt 4 || within address size s.names.table input.offsets.tableSize ||
        s.names.owners.any (fun (_,base) => within address size (base+input.offsets.hash) 16) ||
        within address size (new+input.offsets.index) 4 do
      throw s!"replace write outside footprint: {address}/{size}"
  return ({s with world,binary := r,call := s.call+1},Json.mkObj [
    ("instructions",toJson r.pcs.size),("reads",toJson r.reads.size),("writes",toJson r.writes.size),
    ("coverage",toJson (r.coverage.toList.drop s.binary.coverage.size)),("answer",toJson answer)])

end Binary.Pair.Replace
