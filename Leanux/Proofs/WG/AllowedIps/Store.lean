import Leanux.Proofs.WG.AllowedIps.Tree

/-!
# Exact representation of pure allowed-IP trees

The representation records every reachable node's complete mirror value,
including its two child slots and parent backlink. Unrelated store entries
are permitted. This is a structural relation, not a lookup specification.
-/

namespace Leanux.Proofs.WG.AllowedIps

open Leanux

def encode (width : Nat) (parent : WG.Slot) (n : NodeData) (l r : Tree) : WG.AipNode :=
  { peer := n.peer, bit := #[l.root, r.root], cidr := n.cidr,
    bitlen := width, bits := n.addr, parent }

def RepAt (nodes : Std.TreeMap Nat WG.AipNode) (width : Nat) (parent : WG.Slot) :
    Tree → Prop
  | .empty => True
  | .node n l r => nodes[n.id]? = some (encode width parent n l r) ∧
      RepAt nodes width (.child n.id 0) l ∧ RepAt nodes width (.child n.id 1) r

def Tree.child (l r : Tree) (b : Nat) : Tree := if b = 0 then l else r

@[simp] theorem Tree.child_zero (l r : Tree) : Tree.child l r 0 = l := rfl

@[simp] theorem Tree.child_one (l r : Tree) : Tree.child l r 1 = r := rfl

theorem RepAt.child {nodes : Std.TreeMap Nat WG.AipNode} {width : Nat}
    {parent : WG.Slot} {n : NodeData} {l r : Tree}
    (h : RepAt nodes width parent (.node n l r)) {b : Nat} (hb : b < 2) :
    RepAt nodes width (.child n.id b) (Tree.child l r b) := by
  have cases : b = 0 ∨ b = 1 := by omega
  rcases cases with rfl | rfl
  · exact h.2.1
  · exact h.2.2

theorem Tree.Valid.child {width : Nat} {n : NodeData} {l r : Tree}
    (h : Tree.Valid width (.node n l r)) (b : Nat) :
    (Tree.child l r b).Valid width := by
  unfold Tree.child
  split
  · exact h.2.2.1
  · exact h.2.2.2.1

theorem Tree.child_height_lt (n : NodeData) (l r : Tree) (b : Nat) :
    (Tree.child l r b).height < (Tree.node n l r).height := by
  change (Tree.child l r b).height < max l.height r.height + 1
  unfold Tree.child
  split <;> omega

theorem getNode_run (w : WG.AipStore) (ambient : Ambient) (id : Nat) (n : WG.AipNode)
    (hn : w.nodes[id]? = some n) :
    ((WG.getNode id).run w).run ambient = .ok ((n, w), ambient) := by
  simp [WG.getNode, hn, StateT.run_bind] <;> rfl

theorem encode_bitAt_run {m : Type → Type} [Monad m] [MonadLiftT AmbientM m]
    (width : Nat) (parent : WG.Slot) (n : NodeData)
    (l r : Tree) (b : Nat) (hb : b < 2) :
    ((encode width parent n l r).bitAt b : m (Option WG.NodeId)) =
      pure (Tree.child l r b).root := by
  have cases : b = 0 ∨ b = 1 := by omega
  rcases cases with rfl | rfl <;> rfl

@[simp] theorem NodeData.own_map_id (n : NodeData) :
    n.own.map Entry.id = if n.peer.isSome then some n.id else none := by
  cases hp : n.peer <;> simp [NodeData.own, NodeData.entry, hp]

def Tree.lookupId (width key : Nat) (t : Tree) : Option Nat :=
  (t.lookup width key).map Entry.id

@[simp] theorem Tree.lookupId_empty (width key : Nat) :
    Tree.empty.lookupId width key = none := rfl

theorem Tree.lookupId_node (width key : Nat) (n : NodeData) (l r : Tree) :
    (Tree.node n l r).lookupId width key =
      if prefixBits width n.cidr n.addr = prefixBits width n.cidr key then
        if n.cidr = width then (if n.peer.isSome then some n.id else none)
        else ((Tree.child l r (bit width n.cidr key)).lookupId width key).or
          (if n.peer.isSome then some n.id else none)
      else none := by
  unfold Tree.lookupId
  rw [Tree.lookup]
  unfold Tree.child
  split
  · split
    · simp only [NodeData.own_map_id]
    · split <;> simp only [Option.map_or, NodeData.own_map_id] <;> rfl
  · rfl

end Leanux.Proofs.WG.AllowedIps
