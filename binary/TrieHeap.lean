import AllowedipsLayout
import Leanux.WG.AllowedIps

namespace Binary.AllowedipsRelation
open Leanux.WG
abbrev Address := BitVec 64

/-- Logical identities have physical pointers; NULL remains distinct.
    Unvisited identities need no address constraint. -/
def pointer (addresses : Nat → Address) (id : Option Nat) : Address :=
  id.map addresses |>.getD 0

def common (bits stored query : Nat) : Nat :=
  let x := stored ^^^ query
  if bits = 32 then 32 - fls x
  else if bits = 128 then
    128 - (if x / 2^64 ≠ 0 then fls (x / 2^64) + 64 else fls (x % 2^64))
  else 0

def childIndex (node : AipNode) (query : Nat) : Nat :=
  query / 2 ^ (node.bitlen - 1 - node.cidr) % 2

/-- Only the path this invocation can read belongs to the heap predicate.
    Cycles are not prohibited here: accepted mirror execution supplies the
    bounded-loop termination argument, not an acyclicity premise. -/
inductive Reached (nodes : NodeId → Option AipNode) (root : Option NodeId)
    (bits query : Nat) : NodeId → Prop
  | root (id) (atRoot : root = some id) : Reached nodes root bits query id
  | child (id node next)
      (reached : Reached nodes root bits query id)
      (present : nodes id = some node)
      (prefixMatches : node.cidr ≤ common bits node.bits query)
      (short : node.cidr < bits)
      (link : node.bit[childIndex node query]? = some (some next)) :
      Reached nodes root bits query next

/-- C stores IPv6 as two little-endian machine words, high half first.
    The low half is read only when the high halves agree. -/
def KeyFields (memory : Mem 64) (base : Address) (bits stored query : Nat) : Prop :=
  stored < 2^bits ∧ query < 2^bits ∧
  if bits = 32 then memory.loadInt base 4 = some stored
  else memory.loadInt base 8 = some ((stored / 2^64 : Nat) : Int) ∧
    (stored / 2^64 = query / 2^64 →
      memory.loadInt (base+8) 8 = some ((stored % 2^64 : Nat) : Int))

def KeyReads (base : Address) (bits stored query : Nat) (a : Address) : Prop :=
  if bits = 32 then InRange base 4 a else
    InRange base 8 a ∨ (stored / 2^64 = query / 2^64 ∧ InRange (base+8) 8 a)

/-- The peer word is read only on a matching prefix; child/selector fields
    only when that matching node is not full length. The physical bitlen,
    parent link, list/RCU union and unused key bytes are outside the relation.
    The source width is constrained only where choose reads it; a mismatching
    prefix requires only the actual CIDR byte to be representable. -/
def NodeFields (memory : Mem 64) (nodes peers : Nat → Address)
    (bits query id : Nat) (node : AipNode) : Prop :=
  nodes id ≠ 0 ∧ node.cidr < 256 ∧
  KeyFields memory (nodes id + .ofNat 64 AllowedipsLayout.bits) bits node.bits query ∧
  memory.loadInt (nodes id + .ofNat 64 AllowedipsLayout.cidr) 1 = some node.cidr ∧
  (node.cidr ≤ common bits node.bits query →
    memory.loadInt (nodes id + .ofNat 64 AllowedipsLayout.peer) 8 = some (pointer peers node.peer).toNat ∧
    (∀ pid, node.peer = some pid → peers pid ≠ 0) ∧
    (node.cidr < bits →
      node.bitlen = bits ∧ node.bit.size = 2 ∧
      memory.loadInt (nodes id + .ofNat 64 AllowedipsLayout.bit_at_a) 1 =
        some (node.cidr / 8 ^^^ ((bits / 8 - 1) % 8)) ∧
      memory.loadInt (nodes id + .ofNat 64 AllowedipsLayout.bit_at_b) 1 = some (7-node.cidr%8) ∧
      ∀ next, node.bit[childIndex node query]? = some next →
        memory.loadInt (nodes id + .ofNat 64 (AllowedipsLayout.bit + 8*childIndex node query)) 8 =
          some (pointer nodes next).toNat ∧
        ∀ nid, next = some nid → nodes nid ≠ 0))

def NodeReads (nodes : Nat → Address) (bits query id : Nat) (node : AipNode)
    (a : Address) : Prop :=
  KeyReads (nodes id + .ofNat 64 AllowedipsLayout.bits) bits node.bits query a ∨
  InRange (nodes id + .ofNat 64 AllowedipsLayout.cidr) 1 a ∨
  (node.cidr ≤ common bits node.bits query ∧
    (InRange (nodes id + .ofNat 64 AllowedipsLayout.peer) 8 a ∨
      (node.cidr < bits ∧
        (InRange (nodes id + .ofNat 64 AllowedipsLayout.bit_at_a) 1 a ∨
         InRange (nodes id + .ofNat 64 AllowedipsLayout.bit_at_b) 1 a ∨
         InRange (nodes id + .ofNat 64 (AllowedipsLayout.bit + 8*childIndex node query)) 8 a))))

def TrieHeap (memory : Mem 64) (nodes peers : Nat → Address)
    (view : NodeId → Option AipNode) (root : Option NodeId) (bits query : Nat) : Prop :=
  (bits = 32 ∨ bits = 128) ∧ query < 2^bits ∧
  ∀ id, Reached view root bits query id →
    ∃ node, view id = some node ∧ NodeFields memory nodes peers bits query id node

def TrieReads (nodes : Nat → Address) (view : NodeId → Option AipNode)
    (root : Option NodeId) (bits query : Nat) (a : Address) : Prop :=
  ∃ id node, Reached view root bits query id ∧ view id = some node ∧ NodeReads nodes bits query id node a

theorem KeyFields.frame {before after : Mem 64} {writes : Address → Prop}
    {base : Address} {bits stored query : Nat}
    (same : EqualOutside writes before after)
    (apart : ∀ a, KeyReads base bits stored query a → ¬writes a)
    (fields : KeyFields before base bits stored query) : KeyFields after base bits stored query := by
  obtain ⟨storedBound, queryBound, loaded⟩ := fields
  refine ⟨storedBound, queryBound, ?_⟩
  by_cases family : bits = 32
  · simp only [KeyReads,  family, ↓reduceIte] at apart loaded ⊢
    exact (same.loadInt base 4 (fun i hi => apart _ ⟨i, hi, rfl⟩)).symm.trans loaded
  · simp only [KeyReads, family, ↓reduceIte] at apart loaded ⊢
    refine ⟨(same.loadInt base 8 (fun i hi => apart _ (.inl ⟨i, hi, rfl⟩))).symm.trans loaded.1, ?_⟩
    intro equal
    exact (same.loadInt (base+8) 8 (fun i hi => apart _ (.inr ⟨equal, i, hi, rfl⟩))).symm.trans (loaded.2 equal)

theorem NodeFields.frame {before after : Mem 64} {writes : Address → Prop}
    {nodes peers : Nat → Address} {bits query id : Nat} {node : AipNode}
    (same : EqualOutside writes before after)
    (apart : ∀ a, NodeReads nodes bits query id node a → ¬writes a)
    (fields : NodeFields before nodes peers bits query id node) :
    NodeFields after nodes peers bits query id node := by
  obtain ⟨nonnull, bounded, key, cidr, matching⟩ := fields
  refine ⟨nonnull, bounded,
    key.frame same (fun a h => apart a (.inl h)), ?_, ?_⟩
  · exact (same.loadInt _ 1 (fun i hi => apart _ (.inr (.inl ⟨i, hi, rfl⟩)))).symm.trans cidr
  · intro matched
    obtain ⟨word, peerNonnull, children⟩ := matching matched
    refine ⟨?_, peerNonnull, ?_⟩
    · exact (same.loadInt _ 8
        (fun i hi => apart _ (.inr (.inr ⟨matched, .inl ⟨i, hi, rfl⟩⟩)))).symm.trans word
    · intro short
      obtain ⟨width, size, byteIndex, bitIndex, links⟩ := children short
      refine ⟨width, size, ?_, ?_, ?_⟩
      · exact (same.loadInt _ 1 (fun i hi => apart _
          (.inr (.inr ⟨matched, .inr ⟨short, .inl ⟨i, hi, rfl⟩⟩⟩)))).symm.trans byteIndex
      · exact (same.loadInt _ 1 (fun i hi => apart _
          (.inr (.inr ⟨matched, .inr ⟨short, .inr (.inl ⟨i, hi, rfl⟩)⟩⟩)))).symm.trans bitIndex
      · intro next atNext
        obtain ⟨word, valid⟩ := links next atNext
        refine ⟨?_, valid⟩
        exact (same.loadInt _ 8 (fun i hi => apart _
          (.inr (.inr ⟨matched, .inr ⟨short, .inr (.inr ⟨i, hi, rfl⟩)⟩⟩)))).symm.trans word

theorem TrieHeap.frame {before after : Mem 64} {writes : Address → Prop}
    {nodes peers : Nat → Address} {view : NodeId → Option AipNode}
    {root : Option NodeId} {bits query : Nat}
    (same : EqualOutside writes before after)
    (apart : ∀ a, TrieReads nodes view root bits query a → ¬writes a)
    (heap : TrieHeap before nodes peers view root bits query) :
    TrieHeap after nodes peers view root bits query := by
  refine ⟨heap.1, heap.2.1, ?_⟩
  intro id reached
  obtain ⟨node, present, fields⟩ := heap.2.2 id reached
  exact ⟨node, present, fields.frame same (fun a h => apart a ⟨id, node, reached, present, h⟩)⟩

/-- Following a represented edge does not grow the invocation's footprint. -/
theorem Reached.from_root {view : NodeId → Option AipNode}
    {root : Option NodeId} {bits query start id : Nat}
    (atStart : Reached view root bits query start)
    (reachable : Reached view (some start) bits query id) :
    Reached view root bits query id := by
  induction reachable with
  | root id eq => cases eq; exact atStart
  | child id node next reached present matched short link ih =>
    exact .child id node next ih present matched short link

theorem TrieHeap.subpath {memory : Mem 64} {nodes peers : Nat → Address}
    {view : NodeId → Option AipNode} {root : Option NodeId} {bits query start : Nat}
    (heap : TrieHeap memory nodes peers view root bits query)
    (reached : Reached view root bits query start) :
    TrieHeap memory nodes peers view (some start) bits query := by
  exact ⟨heap.1, heap.2.1, fun id atNode => heap.2.2 id (Reached.from_root reached atNode)⟩

#print axioms KeyFields.frame
#print axioms NodeFields.frame
#print axioms TrieHeap.frame
#print axioms TrieHeap.subpath
end Binary.AllowedipsRelation
