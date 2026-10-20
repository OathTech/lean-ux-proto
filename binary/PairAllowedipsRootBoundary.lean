import PairAllowedipsRoot
import PairAllowedipsPlacement
import PairAllowedipsNames

namespace Binary.Pair.Allowedips.Root
open Leanux Leanux.WG

/-- A finite cover for the initialization tail's stores. The old-node entries
cover only list links, not their untouched records. -/
def writeSpans (names : Names) (s : MachineData) : List Span :=
  [(s.regs.rbx.toNat,72),
   (names.table+(if s.regs.rbp.toNat==32 then 0 else 8),8)]++
  names.trie.nodes.map (fun p => (p.2+56,16))++
  names.trie.peers.map (fun p => (p.2+1096,16))

/-- Executable resources at the post-allocation cut. The old world has already
performed the wrapper's sequence increment; allocation names are extended only
for validating ownership, while reconstruction still reads the old world. -/
def boundary (names : Names) (o : AllowedipsProbe.Offsets) (world : World)
    (machine : MachineState) (key cidr pid : Nat) : Except String Unit := do
  assertAt names o machine.data.dmem world
  let some d := world.wg.dev | throw "root.device"
  let s := machine.data
  let bits := s.regs.rbp.toNat
  require (machine.pc==AllowedipsMutationImage.Add.entry+0x443) "root.entry-pc"
  require (bits==32 || bits==128) "root.family"
  require ((if bits==32 then d.peerAllowedips.root4 else d.peerAllowedips.root6).isNone) "root.nonempty"
  require (s.regs.r14.toNat==(← Trie.address names.trie.peers (some pid))) "root.owner"
  require ((← readNat machine (s.regs.rsp.toNat+16) 4)==cidr && cidr≤bits) "root.saved-cidr"
  let allocated := names.allocated s.regs.rbx.toNat
  (validate allocated o).mapError DecodeError.message
  require ((← readNat machine s.regs.rbx.toNat 72)==0) "root.zero-allocation"
  Placement.queryLocals machine key bits
  require ((← readNat machine (s.regs.rsp.toNat+8) 8)==
    names.table+(if bits==32 then 0 else 8)) "root.saved-slot"
  require (spansApart [(s.regs.r13.toNat,bits/8),(s.regs.rsp.toNat+8,8),(s.regs.rsp.toNat+16,4)]
    (writeSpans allocated s)) "root.local-separation"

def checkBoundary (names : Names) (o : AllowedipsProbe.Offsets) (world : World)
    (key cidr pid : Nat) (states : Array MachineState) : Except String Nat := do
  let some d := world.wg.dev | throw "root.device"
  let expected := {d with peerAllowedips := {d.peerAllowedips with seq:=d.peerAllowedips.seq+1}}
  let source := {world with wg:={world.wg with dev:=some expected}}
  let mut count := 0
  for machine in states do
    if machine.pc==AllowedipsMutationImage.Add.entry+0x443 then
      boundary names o source machine key cidr pid
      count := count+1
  return count

end Binary.Pair.Allowedips.Root
