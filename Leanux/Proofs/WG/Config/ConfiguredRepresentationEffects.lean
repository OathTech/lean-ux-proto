import Leanux.Proofs.WG.Config.ConfiguredOwnerModel

/-! Exact represented trees are determined by their store and root. This
join uses structural representation, not extensional routing lookup. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG AllowedIps

theorem nodeData_equal (a b : NodeData)
    (id : a.id=b.id) (addr : a.addr=b.addr) (cidr : a.cidr=b.cidr)
    (peer : a.peer=b.peer) : a=b := by
  cases a
  cases b
  simp_all

theorem repAt_same_root_unique (nodes : Std.TreeMap Nat AipNode)
    (width : Nat) (parent : Slot) (left right : Tree)
    (one : RepAt nodes width parent left)
    (two : RepAt nodes width parent right)
    (root : left.root=right.root) : left=right := by
  induction left generalizing right parent with
  | empty =>
    cases right with
    | empty => rfl
    | node n l r => cases root
  | node n l r ihl ihr =>
    cases right with
    | empty => cases root
    | node m u v =>
      have id : n.id=m.id := Option.some.inj root
      have stored : encode width parent n l r=encode width parent m u v := by
        have first := one.1
        rw [id] at first
        exact Option.some.inj (first.symm.trans two.1)
      have addr : n.addr=m.addr := congrArg AipNode.bits stored
      have cidr : n.cidr=m.cidr := congrArg AipNode.cidr stored
      have peer : n.peer=m.peer := congrArg AipNode.peer stored
      have eq : n=m := nodeData_equal n m id addr cidr peer
      subst m
      have roots := congrArg AipNode.bit stored
      have rootL : l.root=u.root := by
        have point := congrArg (fun b : Array (Option NodeId) => b[0]?) roots
        simpa [encode] using point
      have rootR : r.root=v.root := by
        have point := congrArg (fun b : Array (Option NodeId) => b[1]?) roots
        simpa [encode] using point
      rw [ihl _ _ one.2.1 two.2.1 rootL, ihr _ _ one.2.2 two.2.2 rootR]

theorem forestRep_unique (d : Device) (a4 a6 b4 b6 : Tree)
    (one : ForestRep d a4 a6) (two : ForestRep d b4 b6) :
    a4=b4 ∧ a6=b6 :=
  ⟨repAt_same_root_unique d.nodes 32 .root4 a4 b4 one.2.2.1 two.2.2.1
      (one.1.symm.trans two.1),
    repAt_same_root_unique d.nodes 128 .root6 a6 b6 one.2.2.2 two.2.2.2
      (one.2.1.symm.trans two.2.1)⟩

theorem configuredOwners_representation (d : Device) (a4 a6 b4 b6 : Tree)
    (one : ForestRep d a4 a6) (two : ForestRep d b4 b6)
    (owners : ConfiguredOwners d a4 a6) : ConfiguredOwners d b4 b6 := by
  obtain ⟨rfl,rfl⟩ := forestRep_unique d a4 a6 b4 b6 one two
  exact owners

end Leanux.Proofs.WG.Config

