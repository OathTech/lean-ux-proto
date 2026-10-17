import ProbeSupport
open Lean

namespace AllowedipsProbe
open Leanux Leanux.WG

structure Offsets where
  nodeSize : Nat
  peer : Nat
  children : Nat
  cidr : Nat
  bitAtA : Nat
  bitAtB : Nat
  bitlen : Nat
  bits : Nat
  peerRefcount : Nat
  deriving FromJson

structure Input where
  instructions : Array Instruction
  labels : Array (String × Nat)
  hooks : Array (Nat × String)
  offsets : Offsets
  entry : Nat
  commonEntry : Nat
  preempt : Nat
  entryPreempt : Nat
  budget : Nat
  trace : Json
  operation : Nat
  deriving FromJson

def nodeAddr (id : NodeId) : Nat := 0xa00000 + id * 0x1000
def keyAddr : Nat := 0xb00000
def nodePointer (node : Option NodeId) : Nat := node.map nodeAddr |>.getD 0

/-- Test fixture from the recorded mirror's lookup read projection. Addresses,
    scratch bytes and entry preempt count are supplied fixture data, not a
    claimed capture of kernel memory. Other WG objects are not materialized. -/
def materialize (d : Device) (o : Offsets) (key width preempt entryPreempt : Nat) : Except String DataMem := do
  unless (width == 32 || width == 128) && key < 2^width do throw "invalid address width"
  let mut m : DataMem := (List.replicate 0x810 (0 : UInt8)).At (.ofNat 64 (stackAddr-0x800))
  m := put m stackAddr 8 stopAddr
  m := put m preempt 4 entryPreempt
  let network := (List.range (width/8)).map fun i => UInt8.ofNat (key / 256^(width/8-1-i) % 256)
  m := m.storeBytes (.ofNat 64 keyAddr) network
  for (id, n) in d.nodes.toList do
    unless id < 256 && (n.bitlen == 32 || n.bitlen == 128) && n.cidr ≤ n.bitlen &&
        n.bits < 2^n.bitlen && n.bit.size == 2 do throw "unrepresentable fixture trie node"
    let a := nodeAddr id
    m := m.storeBytes (.ofNat 64 a) (List.replicate o.nodeSize 0)
    if let some pid := n.peer then
      unless d.peers.contains pid do throw "node names absent peer"
    m := put m (a+o.peer) 8 (nullablePeerAddr n.peer)
    for i in [:2] do
      let child := n.bit[i]!
      if let some childId := child then
        unless d.nodes.contains childId do throw "node names absent child"
      m := put m (a+o.children+i*8) 8 (nodePointer child)
    m := put m (a+o.cidr) 1 n.cidr
    m := put m (a+o.bitAtA) 1 ((n.cidr/8) ^^^ ((n.bitlen/8-1)%8))
    m := put m (a+o.bitAtB) 1 (7-n.cidr%8)
    m := put m (a+o.bitlen) 1 n.bitlen
    if n.bitlen == 32 then m := put m (a+o.bits) 4 n.bits
    else
      m := put m (a+o.bits) 8 (n.bits / 2^64)
      m := put m (a+o.bits+8) 8 (n.bits % 2^64)
  for (id, p) in d.peers.toList do
    unless id < 256 && p.refcount < 2^32 do throw "unrepresentable fixture peer"
    m := put m (peerAddr id+o.peerRefcount) 4 p.refcount
  return materializeServices m

end AllowedipsProbe
