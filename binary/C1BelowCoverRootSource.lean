import C1BelowCoverRootHeap
import C1BelowCoverSource

/-! Result C1, work package 3, covering path at the root: the mirror-side
device after the two connections (the fresh node above `down`, then the
fresh node in the family's root slot) and its projection. -/
namespace Binary.Pair.Allowedips.C1Cover
open Leanux Leanux.WG

/-- Endpoint of the covering insertion at the root, with the mirror's ordered writes. -/
def coverRootInstalled (d : Device) (v4 : Bool) (downId b key cidr width pid : Nat)
    (downNode : AipNode) (owner : Peer) : Device :=
  let fresh := newNode key cidr width (some pid)
  let linked := {fresh with bit:=fresh.bit.set! b (some downId)}
  { d with
    nextNode := d.nextNode+1
    nodes := (((d.nodes.insert d.nextNode fresh).insert downId
        {downNode with parent:=.child d.nextNode b}).insert d.nextNode linked).insert d.nextNode
        {linked with parent:=if v4 then Slot.root4 else Slot.root6}
    peers := d.peers.insert pid {owner with allowedipsList:=owner.allowedipsList++[d.nextNode]}
    peerAllowedips := if v4 then {d.peerAllowedips with root4:=some d.nextNode}
      else {d.peerAllowedips with root6:=some d.nextNode} }

theorem target_coverRootInstalled (d : Device) (v4 : Bool) (downId b key cidr width pid : Nat)
    (downNode : AipNode) (owner : Peer)
    (hasDown : d.nodes.get? downId=some downNode)
    (hasPeer : d.peers.get? pid=some owner)
    (below : ∀ pair ∈ d.nodes.toList, pair.1<d.nextNode) :
    target (coverRootInstalled d v4 downId b key cidr width pid downNode owner)=
      installedCoverRoot v4 downId b key cidr width pid (target d) := by
  have downBelow := below (downId,downNode) (Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hasDown)
  have freshDown : d.nextNode≠downId := Ne.symm (Nat.ne_of_lt downBelow)
  let fresh : AipNode := {newNode key cidr width (some pid) with
    bit:=(newNode key cidr width (some pid)).bit.set! b (some downId),
    parent:=if v4 then Slot.root4 else Slot.root6}
  let lowered : AipNode := {downNode with parent:=.child d.nextNode b}
  have hasDownAfter : (d.nodes.insert d.nextNode fresh).get? downId=some downNode := by
    simpa [Std.TreeMap.getElem?_insert,freshDown] using hasDown
  have sameTree : (coverRootInstalled d v4 downId b key cidr width pid downNode owner).nodes.Equiv
      ((d.nodes.insert d.nextNode fresh).insert downId lowered) := by
    apply Std.TreeMap.Equiv.of_forall_constGet?_eq
    intro current
    simp only [coverRootInstalled,Std.TreeMap.getElem?_insert,lowered,fresh]
    split
    · rename_i atFresh
      have equal : d.nextNode=current := by simpa using atFresh
      subst equal
      simp [Ne.symm freshDown]
    · split
      · simp_all
      · simp_all
  have nodes : (coverRootInstalled d v4 downId b key cidr width pid downNode owner).nodes.toList=
      d.nodes.toList.map (reparent downId (.child d.nextNode b))++[(d.nextNode,fresh)] := by
    rw [sameTree.toList_eq,Trie.tree_insert_present _ downId downNode lowered hasDownAfter,
      tree_insert_max d.nodes d.nextNode fresh below,List.map_append,
      List.map_cons,List.map_nil]
    simp only [freshDown,ite_false]
    apply congrArg (· ++ [(d.nextNode,fresh)])
    apply List.map_congr_left
    rintro ⟨current,node⟩ member
    have found := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp member
    by_cases same : current=downId
    · subst current
      have equal := Option.some.inj (found.symm.trans hasDown)
      subst node
      simp [reparent,lowered]
    · simp [reparent,same]
  have peers : (coverRootInstalled d v4 downId b key cidr width pid downNode owner).peers.toList=
      d.peers.toList.map (fun (current,p) =>
        (current,if current=pid then {owner with allowedipsList:=owner.allowedipsList++[d.nextNode]} else p)) :=
    Trie.tree_insert_present d.peers pid owner _ hasPeer
  have peerProjection : ((coverRootInstalled d v4 downId b key cidr width pid downNode owner).peers.toList.map
      (fun (id,p) => (id,p.refcount,p.allowedipsList)))=(target d).peers.map (appendOwner d.nextNode pid) := by
    rw [peers]
    simp only [target,List.map_map]
    apply List.map_congr_left
    rintro ⟨current,p⟩ present
    by_cases same : current=pid
    · subst current
      have equal := Option.some.inj ((Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp present).symm.trans hasPeer)
      subst owner
      simp [appendOwner]
    · simp [appendOwner,same]
  change ({table:=_,nodes:=_,peers:=_,nextNode:=d.nextNode+1} : State)=_
  rw [nodes,peerProjection]
  cases v4 <;> rfl

#print axioms target_coverRootInstalled
end Binary.Pair.Allowedips.C1Cover
