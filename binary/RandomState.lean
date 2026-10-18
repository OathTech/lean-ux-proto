import Execution
import Memory
import RandomLayout

namespace Binary.RandomProvider
open Layout

/-- Private provider/recording allocations, independent of the WireGuard
allocation interpretation. Remote-node names bound graph traversal, not draws. -/
structure Config where
  blocks : List (Nat × Nat)
  remoteNodes : List Nat := []
  deriving Repr, BEq

def PrivateBytes (c : Config) (address : BitVec 64) : Prop :=
  ∃ span ∈ c.blocks, InRange (.ofNat 64 span.1) span.2 address

/-- Read only the declared private allocation cover. The checker below
cannot inspect undeclared memory or an execution history through this view.
Disjointness from WireGuard storage is a separate physical entry condition. -/
def snapshot : List (Nat × Nat) → DataMem → Option DataMem
  | [],_ => some {}
  | (base,size)::rest,m => do
    let bytes ← m.loadBytes (.ofNat 64 base) size
    let tail ← snapshot rest m
    return tail ∪ bytes.At (.ofNat 64 base)

def read (m : DataMem) (address size : Nat) : Except String Nat := do
  unless address+size≤2^64 do throw "random.private.address-wrap"
  let some value := m.loadInt (.ofNat 64 address) size | throw "random.private.unmapped"
  unless 0≤value && value<2^(8*size) do throw "random.private.word-range"
  return value.toNat

def mapped (m : DataMem) (address size : Nat) : Except String Unit := do
  unless address+size≤2^64 && (m.loadBytes (.ofNat 64 address) size).isSome do
    throw "random.private.region-unmapped"

/-- The initialized path allows cache exhaustion and generation changes.
It does not constrain the entropy values or promise a particular draw. -/
def initialized (m : DataMem) : Except String Unit := do
  let ready ← read m readyAddress 4
  if ready==0 || ready≥2^31 then
    unless (← read m initAddress 4)>1 do throw "random.private.not-initialized"
  mapped m cacheAddress 108
  mapped m cpuAddress 40
  mapped m baseAddress 40

def steer (m : DataMem) (address : Nat) : Except String Unit := do
  if address==0 then return
  -- UP spinlocks occupy no bytes in this image. Counts precede 64 entries.
  let count ← read m (address+steerCount) 4
  let head ← read m (address+steerHead) 4
  unless count≤64 && head≤count do throw "random.private.steering-counts"
  let _ ← read m (address+steerMismatches) 4
  mapped m (address+steerEntries) (count*entrySize)
  for i in [:count] do
    unless (← read m (address+steerEntries+i*entrySize+entryLength) 4)≤40 do
      throw "random.private.steering-payload"

/-- Follow only the selected remote bucket. Repeated or unnamed nodes fail;
the bound is the supplied finite allocation universe, not a retry budget. -/
def remote (c : Config) (m : DataMem) (handle : Nat) : Nat → Nat → List Nat → Except String Nat
  | 0,_,_ => .error "random.private.remote-cycle-or-bound"
  | fuel+1,link,seen => do
    if link==0 then return 0
    unless remoteLink<link && link<2^64 do throw "random.private.remote-link"
    let base := link-remoteLink
    unless c.remoteNodes.contains base && !seen.contains base do
      throw "random.private.remote-node"
    let key ← read m (base+remoteHandle) 8
    if key==handle then
      let object ← read m (base+remoteObject) 8
      unless object != 0 do throw "random.private.remote-object-null"
      return ← read m (object+objectSteer) 8
    remote c m handle fuel (← read m (base+remoteLink) 8) (base::seen)

def recording (c : Config) (m : DataMem) (task : Nat) : Except String Unit := do
  -- Saturated choice recording increments this word, even with no payload write.
  mapped m (task+taskDropped) 4
  let object ← read m (task+taskObject) 8
  let mut selected := 0
  let mut direct := false
  if object != 0 then
    let isRemote ← read m (object+objectRemote) 1
    selected ← read m (object+objectSteer) 8
    direct := isRemote != 0 || selected != 0
  if !direct then
    let handle ← read m (task+taskHandle) 8
    if handle != 0 then
      let bucket := (handle*0x61c8864680b583eb%2^64)/2^60
      let link ← read m (remoteMapAddress+8*bucket) 8
      selected ← remote c m handle (c.remoteNodes.length+1) link []
  steer m selected
  mapped m sequenceAddress 8

/-- Current physical private state only. Coverage/stack readiness and
separation from the private allocations are checked separately at entry. -/
def check (c : Config) (task : Nat) (active : Bool) (m : DataMem) : Except String Unit := do
  unless c.blocks.all (fun (base,size) => 0<size && base+size≤2^64) do
    throw "random.private.allocation-range"
  let some privateMemory := snapshot c.blocks m | throw "random.private.allocation-unmapped"
  initialized privateMemory
  if active then recording c privateMemory task

end Binary.RandomProvider
