import PairIndex
import PairIndexStorage

namespace Binary.Pair.Remove
open Lean Leanux Leanux.WG

def entry : Nat := 0xffffffff813a0400

/-- Removal reads pprev even for an owner absent from every bucket. This
additional projection is computed from memory, independently of the source. -/
def ownership (n : Names) (o : Offsets) (m : DataMem) : Decode (List (IndexOwner × Bool)) :=
  n.owners.mapM fun (owner,a) => do
    return (owner,(← word m "owner.pprev" (a+o.hash+o.pprev) 8) != 0)

def targetOwnership (d : Device) : List (IndexOwner × Bool) :=
  ((d.peers.toList.map (fun p => IndexOwner.handshake p.1)) ++
    (d.keypairs.toList.map (fun p => IndexOwner.keypair p.1))).map
      fun owner => (owner,d.indexTable.any (·.owner == owner))

def assertAt (n : Names) (o : Offsets) (m : DataMem) (w : World) : Except String Unit := do
  unless Index.storageCheck n o do throw "remove: index storage overlaps or wraps"
  assertMemory n o m w
  let some d := w.k.wg | throw "remove: no source device"
  let actual ← (ownership n o m).mapError DecodeError.message
  unless actual == targetOwnership d do throw "remove: owner hashed state differs"

/-- Only constructed fixtures fill the otherwise unmapped unlinked fields.
The removal itself retains memory, including across repeated invocations. -/
def fixture (input : ProbeInput) (w : World) : Except String Session := do
  let s ← startSession input w
  let some d := w.k.wg | throw "remove fixture: no device"
  let mut m := s.binary.state.data.dmem
  for (owner,a) in s.names.owners do
    unless d.indexTable.any (·.owner == owner) do
      m := put (put m (a+input.offsets.hash) 8 0) (a+input.offsets.hash+input.offsets.pprev) 8 0
  assertAt s.names input.offsets m w
  return {s with binary := {s.binary with state := {s.binary.state with data := {s.binary.state.data with dmem := m}}}}

def invoke (input : ProbeInput) (seed : UInt64) (s : Session) (owner : IndexOwner)
    (checkOwnership : Bool := true) : Except String (Session × Json) := do
  let a ← addressOf s.names owner
  let memory := put s.binary.state.data.dmem stackAddr 8 stopAddr
  if checkOwnership then assertAt s.names input.offsets memory s.world
  else assertMemory s.names input.offsets memory s.world
  let initial : MachineState := ⟨{dmem := memory,regs := {
    rdi := .ofNat s.names.table,rsi := .ofNat a,rsp := .ofNat stackAddr,
    rbx := 17,rbp := 34,r12 := 51,r13 := 68,r14 := 85,r15 := 102}},.ofNat entry⟩
  let prior := {s.binary with state := initial,history := #[initial],pcs := #[],reads := #[],writes := #[]}
  let r ← runUntil input.instructions input.labels input.hooks input.preempt initial seed true
    10000 0 #[] (some prior) stopAddr (some #[])
  let (_,world) ← (indexRemove owner).run s.world |>.mapError Stop.message
  if checkOwnership then assertAt s.names input.offsets r.state.data.dmem world
  else assertMemory s.names input.offsets r.state.data.dmem world
  unless r.state.pc.toBitVec.toNat==stopAddr && r.state.data.regs.rsp.toNat==stackAddr+8 do
    throw "remove return: PC/stack"
  for reg in [Reg64.rbx,.rbp,.r12,.r13,.r14,.r15] do
    unless r.state.data.regs.get64 reg==initial.data.regs.get64 reg do throw "remove return: callee save"
  unless (← readNat r.state input.preempt 4)==0 do throw "remove return: preempt"
  unless (← readNat r.state 0xffffffff81cc85e0 2)==0 do throw "remove return: pending"
  unless (← readNat r.state coverageAddr 8)==r.coverage.size do throw "remove return: coverage count"
  for i in [:r.coverage.size] do
    unless (← readNat r.state (coverageAddr+8*(i+1)) 8)==r.coverage[i]! do throw "remove return: coverage word"
  for (address,size) in r.writes do
    unless within address size (stackAddr-0x800) 0x800 || within address size coverageAddr coverageBytes ||
        within address size input.preempt 4 || within address size s.names.table input.offsets.tableSize ||
        s.names.owners.any (fun (_,base) => within address size (base+input.offsets.hash) 16) do
      throw s!"remove write outside footprint: {address}/{size}"
  return ({s with world,binary := r,call := s.call+1},Json.mkObj [
    ("owner",toJson (reprStr owner)),
    ("instructions",toJson r.pcs.size),("reads",toJson r.reads.size),("writes",toJson r.writes.size),
    ("coverage",toJson (r.coverage.toList.drop s.binary.coverage.size)),
    ("hashed",toJson ((s.world.k.wg.map fun d => d.indexTable.any (·.owner==owner)).getD false))])

end Binary.Pair.Remove
