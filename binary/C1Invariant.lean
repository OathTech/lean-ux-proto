import StatementC1Vacuity
import SourceAip
import TrieHeap

/-! Result C1, proof plan: the invariant the proof of `Headline` exhibits, and
the trie ordering facts the insertion cases need, as executable definitions.

`Inv` is the landed relation of `StatementC1Headline.Related`, unchanged. The
ordering facts the trials took as hypotheses are not added to it: they are
*derived*. Two executable predicates state them, and the interface
propositions in `C1Interfaces` are these predicates being `true`:

- `ordered d` (the stored trie): every node has a family width, a prefix
  length within it and a key within it; every child edge keeps the family,
  strictly increases the prefix length, shares the parent's prefix and sits
  on the side the parent's branching bit of the child's key names; each root
  has its slot's family. It follows from `Inv` alone (the edge clauses are
  `Trie.heap`'s `trie.measure`, `trie.prefix` and `trie.branch`; the node
  clauses are `Trie.decodeNode`'s; the root clause is `heap.root-family`).
- `walk d root key cidr bits placed exact` (what `nodePlacement` returned):
  the placed node covers the key with a prefix no longer than `cidr`, and
  the node below it (the root when nothing was placed) is strictly longer
  than `min cidr common`, shares that many bits with the key, and differs
  from the key at bit `common` when `common < cidr`. It follows from
  `ordered d` and the accepted mirror run.

No theorem here: definitions, and the executable checks the packet's test
and the capture's check run after every insertion. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.Statements.C1

/-- THE INVARIANT. The landed executable relation and structural check for
some interpretation whose table and peers are the layout's and whose node
objects are exactly the ones the allocator has handed out, inside the arena,
with the allocator's pending answers the mirror's pending records. -/
def Inv (L : Layout) (A : Allocator) (w : World) (m : Mem 64) : Prop := Related L A w m

/-- A handed-out node ends strictly below the top of the address space. The
landed interpretation check (`Trie.validate`) demands this of every node, and
the stated contract's `AllocResult` promises only `≤` (through the arena
span). See `C1Interfaces.NodeBelowTop`. -/
def belowTop (a : Nat) : Bool := a + nodeSize < 2^64

/-- Every decidable conjunct of `Related` for a given interpretation (`Idle`
is abstract and is not here). -/
def relatedCheck (L : Layout) (names : Allowedips.Names) (w : World) (m : Mem 64) : Except String Unit := do
  require (names.table == L.table) "inv.table"
  require (names.trie.peers == L.peers) "inv.peers"
  (assertAt names Root.nodeOffsets m w).mapError (s!"inv.relation: {·}")
  require (armed w) "inv.armed"
  let some stream := w.ambient.hidden | throw "inv.records"
  require (stream.all fun record => (allocSites.map (·.2)).contains record.site) "inv.record-sites"
  require (spansApart ([(L.table,AllowedipsMutationLayout.tableSize)] ++
    L.peers.map fun (_,a) => (a,Layouts.peerSize)) L.arena) "inv.arena-apart"
  require (names.trie.nodes.all fun node => L.arena.any fun span =>
    span.1 ≤ node.2 && node.2+nodeSize ≤ span.1+span.2) "inv.nodes-in-arena"

/-- One child edge of the stored trie, as `Trie.heap` checks it. -/
def edgeOrdered (parent child : AipNode) (bit : Nat) : Bool :=
  child.bitlen == parent.bitlen && parent.cidr < child.cidr &&
  child.bits / 2^(parent.bitlen-parent.cidr) == parent.bits / 2^(parent.bitlen-parent.cidr) &&
  child.bits / 2^(parent.bitlen-1-parent.cidr) % 2 == bit

/-- The ordering facts of the stored trie. -/
def ordered (d : Device) : Bool :=
  (d.nodes.toList.all fun (_,n) =>
    (n.bitlen == 32 || n.bitlen == 128) && n.cidr ≤ n.bitlen && n.bits < 2^n.bitlen &&
    n.bit.size == 2 &&
    n.bit.toList.zipIdx.all fun (child,bit) => match child with
      | none => true
      | some id => match d.nodes.get? id with
        | none => false
        | some c => edgeOrdered n c bit) &&
  [(d.peerAllowedips.root4,32),(d.peerAllowedips.root6,128)].all fun (root,width) => match root with
    | none => true
    | some id => match d.nodes.get? id with
      | none => false
      | some n => n.bitlen == width

/-- The node below the placement: the root when nothing was placed, else the
placed node's child on the key's side. -/
def below (d : Device) (root : Option NodeId) (key : Nat) (placed : Option NodeId) : Option NodeId :=
  match placed with
  | none => root
  | some id => match d.nodes.get? id with
    | none => none
    | some p => (p.bit[key / 2^(p.bitlen-1-p.cidr) % 2]?).join

/-- What `nodePlacement root key cidr bits` returned, as the insertion cases
use it. `common` is the landed pure `common_bits`. -/
def walk (d : Device) (root : Option NodeId) (key cidr bits : Nat)
    (placed : Option NodeId) (exact : Bool) : Bool :=
  (match placed with
    | none => !exact
    | some id => match d.nodes.get? id with
      | none => false
      | some p => p.bitlen == bits && p.cidr ≤ cidr && (exact == (p.cidr == cidr)) &&
          key / 2^(bits-p.cidr) == p.bits / 2^(bits-p.cidr)) &&
  (exact || match below d root key placed with
    | none => true
    | some id => match d.nodes.get? id with
      | none => false
      | some down =>
        let common := AllowedipsRelation.common bits down.bits key
        let least := min cidr common
        down.bitlen == bits && least < down.cidr &&
        down.bits / 2^(bits-least) == key / 2^(bits-least) &&
        (match placed with
          | none => true
          | some id => match d.nodes.get? id with
            | none => false
            | some p => p.cidr < least) &&
        (cidr ≤ common || (common < bits &&
          down.bits / 2^(bits-1-common) % 2 != key / 2^(bits-1-common) % 2)))

/-- The walk facts for an insertion about to run from world `w`: the mirror's
own `nodePlacement` from the family's root. Silent (ok) where the mirror
does not reach the walk (prefix too long, empty root) or refuses it. -/
def walkCheck (w : World) (family key cidr : Nat) : Except String Unit := do
  let some d := w.wg.dev | throw "walk: no device"
  let bits := if family == 4 then 32 else 128
  let root := if family == 4 then d.peerAllowedips.root4 else d.peerAllowedips.root6
  if cidr > bits || root.isNone then return
  match ((WG.nodePlacement root key cidr bits).run (Source.Aip.store d)).run w.ambient with
  | .error _ => return
  | .ok ((result,_),_) =>
    require (walk d root key cidr bits result.1 result.2)
      s!"walk: the placement facts fail for {family} {key}/{cidr}: {repr result}"

/-- What the tests run after every insertion: the decidable part of `Inv`
for the interpretation the allocations give, the node bound, and the ordering
facts of the mirror's trie. -/
def invCheck (L : Layout) (names : Allowedips.Names) (w : World) (m : Mem 64) : Except String Unit := do
  relatedCheck L names w m
  require (names.trie.nodes.all fun node => belowTop node.2) "inv.node-below-top"
  let some d := w.wg.dev | throw "inv.device"
  require (ordered d) "inv.ordered"

end Binary.Statements.C1.Proof
