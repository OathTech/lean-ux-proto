import PairAllowedipsState
import SourceAip

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

def locals (names : Names) (machine : MachineState) (root : Option NodeId)
    (key cidr bits peer stack : Nat) (acc : Acc) : Except String Unit := do
  unless acc.1.isNone && acc.2.1.isSome do throw "placement.header-source"
  unless machine.data.regs.rbx.toNat == (← Trie.address names.trie.nodes acc.2.1) &&
      (← readNat machine stack 8) == (← Trie.address names.trie.nodes acc.2.2) do
    throw "placement.cursor-parent"
  unless machine.data.regs.rsp.toNat == stack && machine.data.regs.r12.toNat == cidr &&
      machine.data.regs.r15.toNat == bits do throw "placement.stack-cidr-width"
  let slot ← readNat machine (stack+8) 8
  unless slot == names.table+(if bits==32 then AllowedipsMutationLayout.root4 else AllowedipsMutationLayout.root6) &&
      (← readNat machine slot 8) == (← Trie.address names.trie.nodes root) &&
      (← readNat machine (stack+0x18) 8) == peer &&
      (← readNat machine (stack+0x24) 4) == bits &&
      (← readNat machine (stack+0x10) 4) == cidr do throw "placement.saved-inputs"
  let query := machine.data.regs.r13.toNat
  let actual ← if bits==32 then readNat machine query 4 else do
    let high ← readNat machine query 8
    let low ← readNat machine (query+8) 8
    pure (high*2^64+low)
  unless actual==key do throw "placement.query"

/-- Validate the recorded correspondence points against independent execution
of the mirror loop. Snapshots retain the machine heap; no state is rebuilt. -/
def check (names : Names) (o : AllowedipsProbe.Offsets) (entry : Nat) (world : World)
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
  for machine in states do
    unless !finished do throw "placement.multiple-exits"
    assertAt names o machine.data.dmem source
    let pc := machine.pc.toBitVec.toNat
    if pc==entry+0xf7 then
      locals names machine root key cidr width peer stack acc
      let ((step,next),nextAmbient) ← ((iteration key cidr width acc).run entries).run ambient |>.mapError Stop.message
      entries := next; ambient := nextAmbient
      acc := match step with | .done acc | .yield acc => acc
      visits := visits+1
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
