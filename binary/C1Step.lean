import C1Invariant

/-! Result C1, proof plan: one insertion as a pure function of the mirror's
device, the walk's result and the allocation outcomes. This is the hand-over
between the source-side package (which shows that every accepted run of
`Leanux.WG.insert` is `step`, up to `Allowedips.target`) and the path
packages (which show that the compiled code reaches memory related to
`step`'s device). It has no branch the mirror's `add` does not have, and no
monad. No theorem here; `stepCheck` is run by the packet's test and the
capture's check on every insertion. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.Statements.C1

/-- The paths of `add` (allowedips.c:181-250) the caller's conditions admit. -/
inductive Case where
  /-- `cidr > bits`: `-EINVAL` before anything else. -/
  | tooLong
  /-- Empty trie, the allocation at :190 refused. -/
  | rootNoMem
  /-- Empty trie: the new node becomes the root. -/
  | root
  /-- The walk found a node with this prefix: its peer is replaced. -/
  | exact
  /-- The allocation at :205 refused. -/
  | nodeNoMem
  /-- The placed node has no child on the key's side: attach there. -/
  | child
  /-- The new node covers the node below the placement (root or parent). -/
  | cover
  /-- The allocation at :234 refused: unlink, release, `-ENOMEM`. -/
  | splitNoMem
  /-- An intermediate node above the new node and the node below (two allocations). -/
  | split
  deriving Repr, BEq, DecidableEq

structure Step where
  case : Case
  answer : Int
  device : Device
  /-- Allocation records consumed. -/
  consumed : Nat

def bump (d : Device) : Device :=
  {d with peerAllowedips := {d.peerAllowedips with seq := d.peerAllowedips.seq + 1}}

def slotOf (d : Device) : Slot → Option NodeId
  | .root4 => d.peerAllowedips.root4
  | .root6 => d.peerAllowedips.root6
  | .child parent bit => ((d.nodes.get? parent).bind fun n => n.bit[bit]?).join

def setSlot (d : Device) (slot : Slot) (v : Option NodeId) : Device :=
  match slot with
  | .root4 => {d with peerAllowedips := {d.peerAllowedips with root4 := v}}
  | .root6 => {d with peerAllowedips := {d.peerAllowedips with root6 := v}}
  | .child parent bit => match d.nodes.get? parent with
    | some n => {d with nodes := d.nodes.insert parent {n with bit := n.bit.set! bit v}}
    | none => d

/-- `allocNode` when the record says the object was handed out. -/
def alloc (d : Device) (n : AipNode) : Device :=
  {d with nextNode := d.nextNode+1, nodes := d.nodes.insert d.nextNode n}

def addTail (d : Device) (pid : PeerId) (id : NodeId) : Device :=
  match d.peers.get? pid with
  | some p => {d with peers := d.peers.insert pid {p with allowedipsList := p.allowedipsList ++ [id]}}
  | none => d

def delete (d : Device) (id : NodeId) : Device :=
  d.peers.toList.foldl (fun d (pid,p) => if p.allowedipsList.contains id then
    {d with peers := d.peers.insert pid {p with allowedipsList := listRemove p.allowedipsList id}} else d) d

/-- `connect_node`. -/
def connect (d : Device) (slot : Slot) (id : NodeId) : Device :=
  match d.nodes.get? id with
  | some n => setSlot {d with nodes := d.nodes.insert id {n with parent := slot}} slot (some id)
  | none => d

def side (n : AipNode) (key : Nat) : Nat := key / 2 ^ (n.bitlen - 1 - n.cidr) % 2

/-- `choose_and_connect_node`. -/
def chooseConnect (d : Device) (parent node : NodeId) : Device :=
  match d.nodes.get? parent, d.nodes.get? node with
  | some p, some n => connect d (.child parent (side p n.bits)) node
  | _, _ => d

/-- `Leanux.WG.insert family key cidr pid` on device `d`, given what the
walk returned (`placed`, `exact`; ignored where the walk is not reached) and
the outcomes of the pending allocation records, in order. -/
def step (d : Device) (family key cidr pid : Nat) (placed : Option NodeId) (exact : Bool)
    (outcomes : List Bool) : Step :=
  let bits := if family == 4 then 32 else 128
  let root : Slot := if family == 4 then .root4 else .root6
  let d := bump d
  if cidr > bits then ⟨.tooLong,-EINVAL,d,0⟩ else
  match slotOf d root with
  | none => match outcomes with
    | true :: _ => ⟨.root,0,connect (addTail (alloc d (newNode key cidr bits (some pid))) pid d.nextNode) root d.nextNode,1⟩
    | _ => ⟨.rootNoMem,-ENOMEM,d,1⟩
  | some rootId =>
    if exact then
      match placed.bind fun id => (d.nodes.get? id).map fun n => (id,n) with
      | some (id,n) => ⟨.exact,0,addTail (delete {d with nodes := d.nodes.insert id {n with peer := some pid}} id) pid id,0⟩
      | none => ⟨.exact,0,d,0⟩
    else match outcomes with
    | true :: rest =>
      let fresh := d.nextNode
      let d1 := addTail (alloc d (newNode key cidr bits (some pid))) pid fresh
      match (below d (some rootId) key placed).bind fun id => (d.nodes.get? id).map fun n => (id,n) with
      | none => match placed with
        | some p => ⟨.child,0,chooseConnect d1 p fresh,1⟩
        | none => ⟨.child,0,d1,1⟩
      | some (downId,down) =>
        let least := min cidr (AllowedipsRelation.common bits down.bits key)
        if cidr == least then
          let d2 := chooseConnect d1 fresh downId
          ⟨.cover,0,match placed with | none => connect d2 root fresh | some p => chooseConnect d2 p fresh,1⟩
        else match rest with
        | true :: _ =>
          let middle := d1.nextNode
          let d2 := chooseConnect (chooseConnect (alloc d1 (newNode key least bits none)) middle downId) middle fresh
          ⟨.split,0,match placed with | none => connect d2 root middle | some p => chooseConnect d2 p middle,2⟩
        | _ => ⟨.splitNoMem,-ENOMEM,{delete d1 fresh with nodes := (delete d1 fresh).nodes.erase fresh},2⟩
    | _ => ⟨.nodeNoMem,-ENOMEM,d,1⟩

/-- The mirror's record site for the k-th allocation of a case (`allocSites`). -/
def Case.sites : Case → List Nat
  | .rootNoMem | .root => [77]
  | .nodeNoMem | .child | .cover => [78]
  | .splitNoMem | .split => [78,79]
  | _ => []

/-- The walk the mirror runs for this insertion, if it reaches one. -/
def walkOf (w : World) (d : Device) (family key cidr : Nat) : Option NodeId × Bool :=
  let bits := if family == 4 then 32 else 128
  let root := if family == 4 then d.peerAllowedips.root4 else d.peerAllowedips.root6
  match ((WG.nodePlacement root key cidr bits).run (Source.Aip.store d)).run w.ambient with
  | .ok ((result,_),_) => result
  | .error _ => (none,false)

/-- What the tests run on every accepted insertion: the mirror's answer, its
device up to `Allowedips.target`, and its pending records are `step`'s. -/
def stepCheck (w : World) (family key cidr pid : Nat) (answer : Int) (w' : World) : Except String Case := do
  let some d := w.wg.dev | throw "step: no device"
  let some d' := w'.wg.dev | throw "step: no device afterwards"
  let some stream := w.ambient.hidden | throw "step: no records"
  let (placed,exact) := walkOf w d family key cidr
  let st := step d family key cidr pid placed exact (stream.map fun record => record.bytes.head? == some 1)
  require (st.answer == answer) s!"step: answer {st.answer} for {repr st.case}, the mirror's is {answer}"
  require (Allowedips.target st.device == Allowedips.target d') s!"step: device differs for {repr st.case}"
  require (w'.ambient.hidden == some (stream.drop st.consumed)) s!"step: records differ for {repr st.case}"
  require ((stream.take st.consumed).map (·.site) == st.case.sites) s!"step: record sites differ for {repr st.case}"
  require (armed w') "step: sites disarmed"
  return st.case

end Binary.Statements.C1.Proof
