import C1BelowCoverReconstruct
import AllowedipsChildSource

/-! Origin: trial T2, `binary-trials/t2/CoverSource.lean` on `task/binary-trials` (unreviewed), copied
under the package prefix with the namespaces suffixed `C1Cover`; proofs unchanged. -/

/-! Trial T2, part 2: the mirror's two `chooseAndConnectNode` calls of the covering
case, run on the pending device, and the projection of the result. -/
namespace Binary.Pair.Allowedips.C1Cover
open Leanux Leanux.WG

/-- The mirror device after the allocation and `list_add_tail`, before any connection. -/
def coverPending (d : Device) (key cidr width pid : Nat) (owner : Peer) : Device :=
  { d with
    nextNode := d.nextNode+1
    nodes := d.nodes.insert d.nextNode (newNode key cidr width (some pid))
    peers := d.peers.insert pid {owner with allowedipsList:=owner.allowedipsList++[d.nextNode]} }

/-- Endpoint of the two connections, with the mirror's ordered node writes. -/
def coverInstalled (d : Device) (downId b parentId direction key cidr width pid : Nat)
    (downNode parentNode : AipNode) (owner : Peer) : Device :=
  let fresh := newNode key cidr width (some pid)
  let linked := {fresh with bit:=fresh.bit.set! b (some downId)}
  { d with
    nextNode := d.nextNode+1
    nodes := ((((d.nodes.insert d.nextNode fresh).insert downId
        {downNode with parent:=.child d.nextNode b}).insert d.nextNode linked).insert d.nextNode
        {linked with parent:=.child parentId direction}).insert parentId
        {parentNode with bit:=parentNode.bit.set! direction (some d.nextNode)}
    peers := d.peers.insert pid {owner with allowedipsList:=owner.allowedipsList++[d.nextNode]} }

theorem cover_connect_run (w : WGWorld) (ambient : Ambient) (d : Device)
    (downId b parentId direction key cidr width pid : Nat) (downNode parentNode : AipNode) (owner : Peer)
    (hasDown : d.nodes[downId]?=some downNode) (hasParent : d.nodes[parentId]?=some parentNode)
    (freshDown : d.nextNode≠downId) (freshParent : d.nextNode≠parentId)
    (different : downId≠parentId)
    (proper : cidr<width) (parentProper : parentNode.cidr<parentNode.bitlen)
    (downChoice : b=downNode.bits/2^(width-1-cidr)%2)
    (parentChoice : direction=key/2^(parentNode.bitlen-1-parentNode.cidr)%2) :
    (((do
      Leanux.WG.liftAip (Leanux.WG.chooseAndConnectNode d.nextNode downId)
      Leanux.WG.liftAip (Leanux.WG.chooseAndConnectNode parentId d.nextNode) : Leanux.WG.M Unit).run
        {w with dev:=some (coverPending d key cidr width pid owner)}).run ambient)=
      .ok (((),{w with dev:=some (coverInstalled d downId b parentId direction key cidr width pid
        downNode parentNode owner)}),ambient) := by
  have small : ¬1<b := by omega
  have smallDirection : ¬1<direction := by omega
  simp [Leanux.WG.chooseAndConnectNode,Leanux.WG.choose,Leanux.WG.getDev,
    Leanux.WG.modifyDev,Leanux.WG.connectNode,Leanux.WG.liftAip,Leanux.WG.getNode,
    Leanux.WG.setNode,Leanux.WG.slotSet,hasDown,hasParent,Std.TreeMap.getElem?_insert,
    different,freshDown,freshParent,Ne.symm freshDown,
    coverInstalled,coverPending,newNode,←downChoice,←parentChoice,small,smallDirection,Nat.not_le.mpr proper,Nat.not_le.mpr parentProper]

#print axioms cover_connect_run

theorem target_coverInstalled (d : Device) (downId b parentId direction key cidr width pid : Nat)
    (downNode parentNode : AipNode) (owner : Peer)
    (hasDown : d.nodes.get? downId=some downNode) (hasParent : d.nodes.get? parentId=some parentNode)
    (hasPeer : d.peers.get? pid=some owner) (different : downId≠parentId)
    (below : ∀ pair ∈ d.nodes.toList, pair.1<d.nextNode) :
    target (coverInstalled d downId b parentId direction key cidr width pid downNode parentNode owner)=
      installedCover downId b parentId direction key cidr width pid (target d) := by
  have downBelow := below (downId,downNode) (Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hasDown)
  have parentBelow := below (parentId,parentNode) (Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hasParent)
  have freshDown : d.nextNode≠downId := Ne.symm (Nat.ne_of_lt downBelow)
  have freshParent : d.nextNode≠parentId := Ne.symm (Nat.ne_of_lt parentBelow)
  let fresh : AipNode := {newNode key cidr width (some pid) with
    bit:=(newNode key cidr width (some pid)).bit.set! b (some downId),parent:=Slot.child parentId direction}
  let lowered : AipNode := {downNode with parent:=.child d.nextNode b}
  let updated : AipNode := {parentNode with bit:=parentNode.bit.set! direction (some d.nextNode)}
  have hasDownAfter : (d.nodes.insert d.nextNode fresh).get? downId=some downNode := by
    simpa [Std.TreeMap.getElem?_insert,freshDown] using hasDown
  have hasParentAfter : ((d.nodes.insert d.nextNode fresh).insert downId lowered).get? parentId=some parentNode := by
    simpa [Std.TreeMap.getElem?_insert,freshParent,different] using hasParent
  have sameTree : (coverInstalled d downId b parentId direction key cidr width pid downNode parentNode owner).nodes.Equiv
      (((d.nodes.insert d.nextNode fresh).insert downId lowered).insert parentId updated) := by
    apply Std.TreeMap.Equiv.of_forall_constGet?_eq
    intro current
    simp only [coverInstalled,Std.TreeMap.getElem?_insert,updated,lowered,fresh]
    split
    · rfl
    · split
      · rename_i notParent atFresh
        have equal : d.nextNode=current := by simpa using atFresh
        subst equal
        simp [Ne.symm freshDown]
      · split
        · simp_all
        · simp_all
  have nodes : (coverInstalled d downId b parentId direction key cidr width pid downNode parentNode owner).nodes.toList=
      d.nodes.toList.map (coverUpdate downId b parentId direction d.nextNode)++[(d.nextNode,fresh)] := by
    rw [sameTree.toList_eq,Trie.tree_insert_present _ parentId parentNode updated hasParentAfter,
      Trie.tree_insert_present _ downId downNode lowered hasDownAfter,
      tree_insert_max d.nodes d.nextNode fresh below,List.map_append,List.map_append,
      List.map_cons,List.map_nil,List.map_cons,List.map_nil,List.map_map]
    simp only [freshDown,freshParent,ite_false]
    apply congrArg (· ++ [(d.nextNode,fresh)])
    apply List.map_congr_left
    rintro ⟨current,node⟩ member
    have found := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp member
    by_cases same : current=downId
    · subst current
      have equal := Option.some.inj (found.symm.trans hasDown)
      subst node
      simp [coverUpdate,reparent,installChild,lowered,different]
    · by_cases parentSame : current=parentId
      · subst current
        have equal := Option.some.inj (found.symm.trans hasParent)
        subst node
        simp [coverUpdate,reparent,installChild,updated,same]
      · simp [coverUpdate,reparent,installChild,same,parentSame]
  have peers : (coverInstalled d downId b parentId direction key cidr width pid downNode parentNode owner).peers.toList=
      d.peers.toList.map (fun (current,p) =>
        (current,if current=pid then {owner with allowedipsList:=owner.allowedipsList++[d.nextNode]} else p)) :=
    Trie.tree_insert_present d.peers pid owner _ hasPeer
  have peerProjection : ((coverInstalled d downId b parentId direction key cidr width pid downNode parentNode owner).peers.toList.map
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
  change ({table:=d.peerAllowedips,nodes:=_,peers:=_,nextNode:=d.nextNode+1} : State)=_
  rw [nodes,peerProjection]
  rfl

#print axioms target_coverInstalled

/-- The memory after the four stores corresponds to the mirror device after
the two connections of the covering case. -/
theorem cover_connect_corresponds {names : Names} {world : World} {machine : MachineState}
    {key cidr pid base downId downBase parentId parentBase b direction : Nat} {memory : DataMem} {d : Device}
    {downNode parentNode : AipNode} {owner : Peer}
    (fields : NodeInit.BoundaryFields names Root.nodeOffsets world machine key cidr pid base)
    (related : Corresponds names Root.nodeOffsets machine.data.dmem d)
    (pending : NodeInit.Pending names machine.data d key cidr pid base memory)
    (downNamed : (downId,downBase) ∈ names.trie.nodes)
    (parentNamed : (parentId,parentBase) ∈ names.trie.nodes)
    (downBit : b<2) (bit : direction<2)
    (hasDown : d.nodes.get? downId=some downNode) (hasParent : d.nodes.get? parentId=some parentNode)
    (hasPeer : d.peers.get? pid=some owner)
    -- `down` hangs below `parent` in a tree (`down = parent->bit[...]`), so they differ.
    (different : downId≠parentId) :
    Corresponds (names.allocated base) Root.nodeOffsets
      (connectMemory (connectMemory memory downBase (base+8+b*8) ((base+8+b*8) ||| b))
        base (parentBase+8+direction*8) ((parentBase+8+direction*8) ||| direction))
      (coverInstalled d downId b parentId direction key cidr machine.data.regs.rbp.toNat pid
        downNode parentNode owner) := by
  unfold Corresponds
  rw [target_coverInstalled d downId b parentId direction key cidr machine.data.regs.rbp.toNat pid
    downNode parentNode owner hasDown hasParent hasPeer different (target_nodes_below related)]
  exact reconstruct_cover_connect fields related pending downNamed parentNamed downBit bit

#print axioms cover_connect_corresponds
end Binary.Pair.Allowedips.C1Cover
