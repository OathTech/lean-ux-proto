import PairAllowedipsState
import SourceAip
import CommonBitsCheck
import PairAllowedipsReadSet
import PairAllowedips
import PairRequire

namespace Binary.Pair.Allowedips.Placement
open Leanux Leanux.WG

abbrev Acc := Option (Option NodeId × Bool) × Option NodeId × Option NodeId

/-- The source loop body with its accumulator exposed. This is the actual
component monad, including its branch records and fail-closed child access. -/
def iteration (key cidr bits : Nat) (acc : Acc) : AipM (ForInStep Acc) := do
  let node := acc.2.1
  let parent := acc.2.2
  match node with
  | none =>
    let _ ← branch .placementNode false
    return .done (some (parent,false),node,parent)
  | some id =>
    let _ ← branch .placementNode true
    let id ← pure id
    let n ← getNode id
    if !(← branchCmp .placementCidrLe (n.cidr ≤ cidr) n.cidr cidr) then
      return .done (some (parent,false),node,parent)
    if !(← branch .placementPrefixMatches (← prefixMatches n key bits)) then
      return .done (some (parent,false),node,parent)
    let parent := some id
    if ← branchCmp .placementExact (n.cidr == cidr) n.cidr cidr then
      return .done (some (parent,true),node,parent)
    let next ← n.bitAt (← choose n key)
    return .yield (none,next,parent)

def run (root : Option NodeId) (key cidr bits : Nat) : AipM (Option NodeId × Bool) := do
  let acc ← forIn ([:130] : Std.Legacy.Range) (none,root,none) (fun _ => iteration key cidr bits)
  match acc.1 with
  | some result => return result
  | none => invariant "node_placement deeper than MAX_ALLOWEDIPS_DEPTH"

def cursorLocals (names : Names) (machine : MachineState) (acc : Acc) : Except String Unit := do
  require (acc.1.isNone && acc.2.1.isSome) "placement.header-source"
  require (machine.data.regs.rbx.toNat == (← Trie.address names.trie.nodes acc.2.1) &&
      (← readNat machine machine.data.regs.rsp.toNat 8) ==
        (← Trie.address names.trie.nodes acc.2.2)) "placement.cursor-parent"

def savedLocals (names : Names) (machine : MachineState) (root : Option NodeId)
    (cidr bits peer stack : Nat) : Except String Unit := do
  require (machine.data.regs.rsp.toNat == stack && machine.data.regs.r12.toNat == cidr &&
      machine.data.regs.r15.toNat == bits) "placement.stack-cidr-width"
  let slot ← readNat machine (stack+8) 8
  require (slot == names.table+(if bits==32 then AllowedipsMutationLayout.root4 else AllowedipsMutationLayout.root6) &&
      (← readNat machine slot 8) == (← Trie.address names.trie.nodes root) &&
      (← readNat machine (stack+0x18) 8) == peer &&
      (← readNat machine (stack+0x24) 4) == bits &&
      (← readNat machine (stack+0x10) 4) == cidr) "placement.saved-inputs"

def query4 (machine : MachineState) (key : Nat) : Except String Unit := do
  require ((← readNat machine machine.data.regs.r13.toNat 4)==key) "placement.query"

def query6 (machine : MachineState) (key : Nat) : Except String Unit := do
  let high ← readNat machine machine.data.regs.r13.toNat 8
  let low ← readNat machine (machine.data.regs.r13.toNat+8) 8
  require (high*2^64+low==key) "placement.query"

def queryLocals (machine : MachineState) (key bits : Nat) : Except String Unit :=
  if bits==32 then query4 machine key else query6 machine key

def locals (names : Names) (machine : MachineState) (root : Option NodeId)
    (key cidr bits peer stack : Nat) (acc : Acc) : Except String Unit := do
  cursorLocals names machine acc
  savedLocals names machine root cidr bits peer stack
  queryLocals machine key bits

def writes (c : CommonBitsCoverage.Context) (machine : MachineState) : List Span :=
  [((machine.data.regs.rsp.toBitVec-48).toNat,56)]++Trie.writeSpans c

/-- The executable boundary used by the loop proof. Memory assertions only:
neither an execution nor a predicted postcondition is supplied. -/
def header (names : Names) (o : AllowedipsProbe.Offsets) (c : CommonBitsCoverage.Context)
    (world : World) (machine : MachineState) (root : Option NodeId)
    (key cidr bits peer stack : Nat) (acc : Acc) : Except String Unit := do
  assertAt names o machine.data.dmem world
  Trie.callInput names.trie o machine.data.dmem root bits key
  locals names machine root key cidr bits peer stack acc
  require (machine.pc == AllowedipsMutationImage.Add.entry+0xf7) "placement.header-pc"
  require (cidr≤bits) "placement.header-cidr"
  require (Trie.frameCheck c machine.data) "placement.callback-frame"
  require (spansApart (Trie.readSpans c) [((machine.data.regs.rsp.toBitVec-48).toNat,56)]) "placement.service-separation"
  require (spansApart (readSpans names o) (writes c machine)) "placement.heap-separation"
  require (spansApart [(machine.data.regs.r13.toNat,bits/8)] (writes c machine)) "placement.query-separation"
  require (spansApart [(stack+8,8),(stack+0x10,4),(stack+0x18,8),(stack+0x24,4)]
      (writes c machine)) "placement.saved-input-separation"

/-- Validate the recorded correspondence points against independent execution
of the mirror loop. Snapshots retain the machine heap; no state is rebuilt. -/
def check (names : Names) (o : AllowedipsProbe.Offsets) (c : CommonBitsCoverage.Context)
    (entry : Nat) (world : World)
    (family key cidr pid entryStack : Nat) (states : Array MachineState) : Except String Nat := do
  let some d := world.wg.dev | throw "placement.device"
  let width := if family==4 then 32 else 128
  let root := if family==4 then d.peerAllowedips.root4 else d.peerAllowedips.root6
  let expected := {d with peerAllowedips := {d.peerAllowedips with seq := d.peerAllowedips.seq+1}}
  let source := {world with wg := {world.wg with dev := some expected}}
  let peer ← Trie.address names.trie.peers (some pid)
  let stack := entryStack-(if family==4 then 144 else 152)
  let mut entries := Source.Aip.store expected
  let mut ambient := world.ambient
  let mut acc : Acc := (none,root,none)
  let mut visits := 0
  let mut finished := false
  let mut current : Option NodeId := none
  for machine in states do
    unless !finished do throw "placement.multiple-exits"
    assertAt names o machine.data.dmem source
    let pc := machine.pc.toBitVec.toNat
    if pc==entry+0xf7 then
      header names o c source machine root key cidr width peer stack acc
      current := acc.2.1
      let ((step,next),nextAmbient) ← ((iteration key cidr width acc).run entries).run ambient |>.mapError Stop.message
      entries := next; ambient := nextAmbient
      acc := match step with | .done acc | .yield acc => acc
      visits := visits+1
    else if pc==entry+0x9c then
      let some id := current | throw "placement.common-without-header"
      let some node := d.nodes.get? id | throw "placement.common-node"
      let i := Common.callInput machine.data width node.bits key (machine.pc+5)
      unless Common.callerCheck i c machine.data (machine.pc+5) do
        throw "placement.common-caller"
    else
      unless pc==entry+0x120 || pc==entry+0x3ca do throw "placement.unknown-cut"
      if acc.1.isNone && acc.2.1.isNone then
        let ((step,next),nextAmbient) ← ((iteration key cidr width acc).run entries).run ambient |>.mapError Stop.message
        entries := next; ambient := nextAmbient
        acc := match step with | .done acc | .yield acc => acc
      let some (parent,exact) := acc.1 | throw "placement.exit-before-source"
      unless (pc==entry+0x3ca)==exact &&
          machine.data.regs.rbx.toNat == (← Trie.address names.trie.nodes parent) do
        throw "placement.result"
      finished := true
  unless finished == (root.isSome && cidr≤width) do throw "placement.missing-or-unexpected-loop"
  return visits

end Binary.Pair.Allowedips.Placement
