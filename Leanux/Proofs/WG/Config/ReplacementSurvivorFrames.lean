import Leanux.Proofs.WG.Config.AllowedRemovalEffects
import Leanux.Proofs.WG.Config.ReplacementSurvivorModel

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

theorem writeNode_removalView (d : Device) (id tracked : NodeId) (old new : AipNode)
    (resident : d.nodes[id]? = some old) (same : removalNodeView new = removalNodeView old) :
    (writeNode d id new).nodes[tracked]?.map removalNodeView =
      d.nodes[tracked]?.map removalNodeView := by
  by_cases equal : tracked = id
  · subst tracked
    simp [writeNode, resident, same]
  · simp [writeNode, Std.TreeMap.getElem?_insert, Ne.symm equal]

theorem slotWrite_removalView {d final : Device} {slot : Slot} {value : Option NodeId}
    (write : SlotWrite d slot value final) (tracked : NodeId) :
    final.nodes[tracked]?.map removalNodeView = d.nodes[tracked]?.map removalNodeView := by
  cases write with
  | root4 => rfl
  | root6 => rfl
  | child parent bit n value resident valid shape =>
    exact writeNode_removalView d parent tracked n _ resident rfl

theorem childReparent_removalView {d final : Device} {child : Option NodeId} {slot : Slot}
    (write : ChildReparent d child slot final) (tracked : NodeId) :
    final.nodes[tracked]?.map removalNodeView = d.nodes[tracked]?.map removalNodeView := by
  cases write with
  | none => rfl
  | some id n slot resident => exact writeNode_removalView d id tracked n _ resident rfl

/-- Removal cannot erase a different resident node with a non-null owner.
All serialized fields and that actual owner word survive; no list ownership or
trie reachability invariant is assumed. -/
theorem nodeRemoval_protected_survivor {d final : Device} {id : NodeId} {n : AipNode}
    (step : NodeRemoval d id n final) (tracked : NodeId) (old : AipNode)
    (different : tracked ≠ id) (resident : d.nodes[tracked]? = some old)
    (nonNull : old.peer.isSome = true) :
    ∃ current, final.nodes[tracked]? = some current ∧
      removalNodeView current = removalNodeView old := by
  apply Option.map_eq_some_iff.mp
  have cleared : (writeNode d id {n with peer := none}).nodes[tracked]?.map removalNodeView =
      some (removalNodeView old) := by
    simp [writeNode, Std.TreeMap.getElem?_insert, Ne.symm different, resident]
  cases step with
  | branching left right shape => exact cleared
  | unary child c side shape childRead linked write remaining present =>
    have updated := writeNode_removalView (writeNode d id {n with peer := none}) child tracked
      c {c with parent := n.parent} childRead rfl
    have linkedView := (slotWrite_removalView write tracked).trans (updated.trans cleared)
    simpa [Std.TreeMap.getElem?_erase, different, Ne.symm different] using linkedView
  | leaf linked shape write choice remaining present =>
    have linkedView := (slotWrite_removalView write tracked).trans cleared
    simpa [Std.TreeMap.getElem?_erase, different, Ne.symm different] using linkedView
  | collapse detached promoted linked parent bit pn leaf pnAfter remaining sibling shape location unlink choice
      parentRead siblingRead leafRead parentAfter reparent write present =>
    have detachedView := (slotWrite_removalView unlink tracked).trans cleared
    have parentNull : pn.peer = none := by
      have general : ∀ (slot : Slot) (b : Bool), ParentChoice detached slot b →
          b = true → slot = .child parent bit → nodeOwner detached parent = none := by
        intro slot b h yes equal
        cases h with
        | root4 => cases equal
        | root6 => cases equal
        | child parentId side current read =>
          cases equal
          simpa [nodeOwner, read] using (Option.isNone_iff_eq_none.mp yes)
      simpa [nodeOwner, parentRead] using general n.parent true choice rfl location
    have notParent : tracked ≠ parent := by
      intro equal
      subst tracked
      rw [parentRead] at detachedView
      have same := congrArg Prod.fst (Option.some.inj detachedView)
      have empty : old.peer = none := same.symm.trans parentNull
      simp [empty] at nonNull
    have afterLeaf : ({detached with nodes := detached.nodes.erase id} : Device).nodes[tracked]?.map removalNodeView =
        some (removalNodeView old) := by
      simpa [Std.TreeMap.getElem?_erase, different, Ne.symm different] using detachedView
    have linkedView := (slotWrite_removalView write tracked).trans
      ((childReparent_removalView reparent tracked).trans afterLeaf)
    simpa [Std.TreeMap.getElem?_erase, notParent, Ne.symm notParent] using linkedView

/-- Ordered removals preserve every nonremoved resident node with an owner word,
including when other removed nodes or their parents alias one another. -/
theorem removalRun_protected_survivor {d final : Device} {ids : List NodeId}
    (steps : RemovalRun d ids final) (tracked : NodeId) (old : AipNode)
    (outside : tracked ∉ ids) (resident : d.nodes[tracked]? = some old)
    (nonNull : old.peer.isSome = true) :
    ∃ current, final.nodes[tracked]? = some current ∧
      removalNodeView current = removalNodeView old := by
  induction steps generalizing old with
  | nil d => exact ⟨old, resident, rfl⟩
  | cons d id rest n next final read step tail ih =>
    have different : tracked ≠ id := by
      intro same
      exact outside (List.mem_cons.mpr (Or.inl same))
    have restOutside : tracked ∉ rest := by
      intro member
      exact outside (List.mem_cons.mpr (Or.inr member))
    have listed := congrArg Device.nodes (deleteListedNodes_withoutPeers id d d.peers.toList)
    have listedRead : (deleteListedNodes id d d.peers.toList).nodes[tracked]? = some old := by
      simpa only [withoutPeers] using (congrArg (fun nodes => nodes[tracked]?) listed).trans resident
    obtain ⟨middle, middleRead, middleView⟩ :=
      nodeRemoval_protected_survivor step tracked old different listedRead nonNull
    have middleNonNull : middle.peer.isSome = true := by
      have owner := congrArg Prod.fst middleView
      simpa only [removalNodeView] using (congrArg Option.isSome owner).trans nonNull
    obtain ⟨last, lastRead, lastView⟩ := ih middle restOutside middleRead middleNonNull
    exact ⟨last, lastRead, lastView.trans middleView⟩

/-- The sequence increment does not affect protected survivor serialization. -/
theorem removalEffect_protected_survivor {d final : Device} {ids : List NodeId}
    (steps : RemovalEffect d ids final) (tracked : NodeId) (old : AipNode)
    (outside : tracked ∉ ids) (resident : d.nodes[tracked]? = some old)
    (nonNull : old.peer.isSome = true) :
    ∃ current, final.nodes[tracked]? = some current ∧
      removalNodeView current = removalNodeView old := by
  cases ids with
  | nil => subst final; exact ⟨old, resident, rfl⟩
  | cons id rest =>
    exact removalRun_protected_survivor steps tracked old outside resident nonNull

/-- Readable, owned entries which remain in a peer's filtered allowed-IP list
still have readable nodes with the same owner and serialization fields. -/
theorem removalEffect_readable_survivors {d final : Device} {ids : List NodeId}
    (steps : RemovalEffect d ids final) (p : Peer) (nodes : NodeId → AipNode)
    (readable : ∀ id ∈ p.allowedipsList, d.nodes[id]? = some (nodes id))
    (owned : ∀ id ∈ p.allowedipsList, id ∉ ids → (nodes id).peer.isSome = true) :
    ∀ id ∈ (erasePeerList ids p).allowedipsList,
      ∃ current, final.nodes[id]? = some current ∧
        removalNodeView current = removalNodeView (nodes id) := by
  intro id member
  rw [erasePeerList_allowedips] at member
  obtain ⟨listed, survives⟩ := List.mem_filter.mp member
  have outside : id ∉ ids := by simpa using survives
  exact removalEffect_protected_survivor steps id (nodes id) outside
    (readable id listed) (owned id listed outside)

end Leanux.Proofs.WG.Config
