import PairAllowedipsNodeInit
import PairAllowedipsRootBoundary
import AllowedipsStorage

namespace Binary.Pair.Allowedips.NodeInit
open Leanux Leanux.WG

def writeSpans (names : Names) (s : MachineData) (base : Nat) : List Span :=
  [(base,72),(s.regs.rsp.toNat+36,1),(s.regs.rsp.toNat+43,1),(s.regs.rsp.toNat+44,1)]++
  names.trie.nodes.map (fun p => (p.2+56,16))++
  names.trie.peers.map (fun p => (p.2+1096,16))

/-- Resources before initializing the first allocation of a nonempty insert.
The old relation excludes the uninitialized allocation; only ownership
validation uses its extended names. Stack bytes are checked for readability,
not prescribed values. -/
def boundary (names : Names) (o : AllowedipsProbe.Offsets) (world : World)
    (machine : MachineState) (key cidr pid : Nat) : Except String Nat := do
  assertAt names o machine.data.dmem world
  let s := machine.data
  let bits := s.regs.rbp.toNat
  let base ← readNat machine s.regs.rsp.toNat 8
  require (machine.pc==AllowedipsMutationImage.Add.entry+0x156) "node-init.entry-pc"
  require (bits==32 || bits==128) "node-init.family"
  require (s.regs.r14.toNat==(← Trie.address names.trie.peers (some pid))) "node-init.owner"
  require ((← readNat machine (s.regs.rsp.toNat+16) 4)==cidr && cidr≤bits) "node-init.saved-cidr"
  require (s.regs.r12.toNat==cidr && s.regs.r15.toNat==bits) "node-init.saved-registers"
  let allocated := names.allocated base
  (validate allocated o).mapError DecodeError.message
  require ((← readNat machine base 72)==0) "node-init.zero-allocation"
  Placement.queryLocals machine key bits
  for offset in [36,43,44] do
    require ((s.dmem.loadInt (.ofNat 64 (s.regs.rsp.toNat+offset)) 1).isSome) "node-init.stack-byte-unmapped"
  require (spansApart [(s.regs.r13.toNat,bits/8)] (writeSpans allocated s base)) "node-init.query-separation"
  require (spansApart [(s.regs.rsp.toNat+36,1),(s.regs.rsp.toNat+43,1),(s.regs.rsp.toNat+44,1)]
    ([(base,72),(names.table,24)]++allocations names o)) "node-init.stack-separation"
  return base

def checkBoundary (names : Names) (o : AllowedipsProbe.Offsets) (world : World)
    (key cidr pid : Nat) (states : Array MachineState) : Except String Nat := do
  let some d := world.wg.dev | throw "node-init.device"
  let expected := {d with peerAllowedips:={d.peerAllowedips with seq:=d.peerAllowedips.seq+1}}
  let source := {world with wg:={world.wg with dev:=some expected}}
  let mut pending : Option (Nat × Nat) := none
  let mut count := 0
  for machine in states do
    if machine.pc==AllowedipsMutationImage.Add.entry+0x156 then
      require pending.isNone "node-init.boundary-repeated"
      let base ← boundary names o source machine key cidr pid
      pending := some (base,machine.data.regs.rbp.toNat)
    else if machine.pc==AllowedipsMutationImage.Add.entry+0x1ff then
      let some (base,bits) := pending | throw "node-init.boundary-missing"
      let core ← (Trie.decodeNode (names.allocated base).trie o machine.data.dmem base).mapError DecodeError.message
      require (core==Trie.targetNode (newNode key cidr bits (some pid))) "node-init.record-reconstruction"
      pending := none
      count := count+1
  require pending.isNone "node-init.boundary-unfinished"
  return count

end Binary.Pair.Allowedips.NodeInit
