import PairAllowedipsNodeBoundary

namespace Binary.Pair.Allowedips.ChildResources
open Leanux Leanux.WG CommonBitsCoverage

def callbackSpans (s : MachineData) (c : Context) : List Span :=
  [((s.regs.rsp.toBitVec-8).toNat,8)]++Trie.writeSpans c

def setupSpans (s : MachineData) (c : Context) : List Span :=
  [(s.regs.rsp.toNat,32)]++callbackSpans s c

def publishSpans (s : MachineData) (base : Nat) : List Span :=
  [(base+48,8),(s.regs.rbx.toNat+8,16)]

/-- Executable caller resources for the continuous child path. The existing
initialization boundary supplies reconstruction and allocation contents; these
checks supply mapped stack storage and the concrete read/write separations. -/
def resources (names : Names) (o : AllowedipsProbe.Offsets) (c : Context)
    (s : MachineData) (base : Nat) : Except String Unit := do
  require (s.regs.rsp.toNat+32≤2^64) "child.stack-extent"
  require ((s.dmem.loadInt s.regs.rsp.toBitVec 32).isSome) "child.stack-unmapped"
  require (Trie.frameCheck c s) "child.callback-ready"
  require (spansApart (Trie.readSpans c)
    (NodeInit.writeSpans (names.allocated base) s base++[(s.regs.rsp.toNat,32)]++publishSpans s base))
    "child.callback-input-separation"
  require (spansApart [(s.regs.rsp.toNat,32)] (callbackSpans s c)) "child.saved-input-separation"
  require (spansApart (readSpans (names.allocated base) o++[(names.table,24),(s.regs.r13.toNat,s.regs.rbp.toNat/8)])
    (setupSpans s c)) "child.projection-query-separation"
  require (spansApart (publishSpans s base) (callbackSpans s c)) "child.destination-separation"
  require (spansApart [(s.regs.rsp.toNat+16,8)] [(base+48,8)]) "child.saved-index-separation"

/-- Check the child case identified from the mirror's parent and key. Other
insertion cases remain explicit alternatives and are checked by their own
segment tests; malformed parent/child references always fail. -/
def check (names : Names) (o : AllowedipsProbe.Offsets) (world : World) (key cidr pid : Nat)
    (states : Array MachineState) : Except String Nat := do
  let some d := world.wg.dev | throw "child.device"
  let incremented := {d with peerAllowedips:={d.peerAllowedips with seq:=d.peerAllowedips.seq+1}}
  let source := {world with wg:={world.wg with dev:=some incremented}}
  let mut count := 0
  for machine in states do
    if machine.pc==AllowedipsMutationImage.Add.entry+0x156 then
      match ← (Trie.pointer names.trie.nodes "child.parent" machine.data.regs.rbx.toNat).mapError DecodeError.message with
      | none => pure ()
      | some parentId =>
        let some parent := d.nodes.get? parentId | throw "child.parent-node"
        let direction := key/2^(parent.bitlen-1-parent.cidr)%2
        let some child := parent.bit[direction]? | throw "child.parent-slot"
        match child with
        | some _ => pure ()
        | none =>
          require (parent.bitlen==machine.data.regs.rbp.toNat && parent.cidr<cidr &&
            key/2^(parent.bitlen-parent.cidr)==parent.bits/2^(parent.bitlen-parent.cidr)) "child.source-case"
          let base ← NodeInit.boundary names o source machine key cidr pid
          let c ← Common.readContext machine.data.dmem
          resources names o c machine.data base
          count := count+1
  return count

end Binary.Pair.Allowedips.ChildResources
