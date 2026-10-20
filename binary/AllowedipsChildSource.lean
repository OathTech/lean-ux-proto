import AllowedipsChildReconstruct

namespace Binary.Pair.Allowedips
open Leanux Leanux.WG

/-- Exact execution of the actual mirror connection primitive. The order of
the fresh record's parent write and the old parent's child write is retained. -/
theorem connectNode_child_run (store : AipStore) (ambient : Ambient)
    (id parentId direction : Nat) (node parentNode : AipNode)
    (hasNode : store.nodes.get? id=some node) (hasParent : store.nodes.get? parentId=some parentNode)
    (different : id≠parentId) (bit : direction<2) :
    ((Leanux.WG.connectNode (.child parentId direction) id).run store).run ambient=
      .ok (((),{store with
        nodes := (store.nodes.insert id {node with parent:=.child parentId direction}).insert parentId
          {parentNode with bit:=parentNode.bit.set! direction (some id)}}),ambient) := by
  have hn : store.nodes[id]?=some node := hasNode
  have hp : store.nodes[parentId]?=some parentNode := hasParent
  simp [Leanux.WG.connectNode,Leanux.WG.getNode,Leanux.WG.setNode,Leanux.WG.slotSet,
    hn,hp,Std.TreeMap.getElem?_insert,different,show ¬direction>1 from by omega]

/-- Endpoint of allocation, owner-list append and child connection, preserving
the actual mirror's ordered node writes for the source-side composition. -/
def childInstalled (d : Device) (parentId direction key cidr width pid : Nat)
    (parentNode : AipNode) (owner : Peer) : Device :=
  let fresh := newNode key cidr width (some pid)
  { d with
    nextNode := d.nextNode+1
    nodes := ((d.nodes.insert d.nextNode fresh).insert d.nextNode
      {fresh with parent:=.child parentId direction}).insert parentId
        {parentNode with bit:=parentNode.bit.set! direction (some d.nextNode)}
    peers := d.peers.insert pid {owner with allowedipsList:=owner.allowedipsList++[d.nextNode]} }

theorem install_child_run (w : WGWorld) (ambient : Ambient) (d : Device)
    (parentId direction key cidr width pid : Nat) (parentNode : AipNode) (owner : Peer)
    (hasParent : d.nodes[parentId]?=some parentNode) (hasPeer : d.peers[pid]?=some owner)
    (different : d.nextNode≠parentId) (bit : direction<2) :
    (((do
      Leanux.WG.listAddTail pid d.nextNode
      Leanux.WG.liftAip (Leanux.WG.connectNode (.child parentId direction) d.nextNode) : Leanux.WG.M Unit).run
        {w with dev:=some {d with
          nextNode:=d.nextNode+1
          nodes:=d.nodes.insert d.nextNode (newNode key cidr width (some pid))}}).run ambient)=
      .ok (((),{w with dev:=some (childInstalled d parentId direction key cidr width pid parentNode owner)}),ambient) := by
  simp [Leanux.WG.listAddTail,Leanux.WG.getPeer,Leanux.WG.getDev,Leanux.WG.setPeer,
    Leanux.WG.modifyDev,Leanux.WG.connectNode,Leanux.WG.liftAip,Leanux.WG.getNode,
    Leanux.WG.setNode,Leanux.WG.slotSet,hasParent,hasPeer,Std.TreeMap.getElem?_insert,
    different,show ¬direction>1 from by omega,childInstalled]

theorem target_childInstalled (d : Device) (parentId direction key cidr width pid : Nat)
    (parentNode : AipNode) (owner : Peer)
    (hasParent : d.nodes.get? parentId=some parentNode) (hasPeer : d.peers.get? pid=some owner)
    (below : ∀ pair ∈ d.nodes.toList, pair.1<d.nextNode) :
    target (childInstalled d parentId direction key cidr width pid parentNode owner)=
      installedChild parentId direction key cidr width pid (target d) := by
  have parentBelow := below (parentId,parentNode) (Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hasParent)
  have different : d.nextNode≠parentId := Ne.symm (Nat.ne_of_lt parentBelow)
  let fresh := {newNode key cidr width (some pid) with parent:=Slot.child parentId direction}
  let updated := {parentNode with bit:=parentNode.bit.set! direction (some d.nextNode)}
  have hasParentAfter : (d.nodes.insert d.nextNode fresh).get? parentId=some parentNode := by
    simpa [Std.TreeMap.getElem?_insert,different] using hasParent
  have sameTree : (childInstalled d parentId direction key cidr width pid parentNode owner).nodes.Equiv
      ((d.nodes.insert d.nextNode fresh).insert parentId updated) := by
    apply Std.TreeMap.Equiv.of_forall_constGet?_eq
    intro current
    simp only [childInstalled,Std.TreeMap.getElem?_insert,updated,fresh]
    split
    · rfl
    · split
      · simp_all only
      · simp_all only

  have nodes : (childInstalled d parentId direction key cidr width pid parentNode owner).nodes.toList=
      d.nodes.toList.map (installChild parentId direction d.nextNode)++[(d.nextNode,fresh)] := by
    rw [sameTree.toList_eq,Trie.tree_insert_present _ parentId parentNode updated hasParentAfter,
      tree_insert_max d.nodes d.nextNode fresh below,List.map_append,List.map_cons,List.map_nil]
    simp only [different,ite_false]
    apply congrArg (· ++ [(d.nextNode,fresh)])
    apply List.map_congr_left
    rintro ⟨current,node⟩ member
    by_cases same : current=parentId
    · subst current
      have equal := Option.some.inj ((Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp member).symm.trans hasParent)
      subst node
      simp [installChild,updated]
    · simp [installChild,same]
  have peers : (childInstalled d parentId direction key cidr width pid parentNode owner).peers.toList=
      d.peers.toList.map (fun (current,p) =>
        (current,if current=pid then {owner with allowedipsList:=owner.allowedipsList++[d.nextNode]} else p)) :=
    Trie.tree_insert_present d.peers pid owner _ hasPeer
  have peerProjection : ((childInstalled d parentId direction key cidr width pid parentNode owner).peers.toList.map
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

#print axioms connectNode_child_run
#print axioms install_child_run
#print axioms target_childInstalled

theorem child_connect_corresponds {names : Names} {world : World} {machine : MachineState}
    {key cidr pid base parentId parentBase direction : Nat} {memory : DataMem} {d : Device}
    {parentNode : AipNode} {owner : Peer}
    (fields : NodeInit.BoundaryFields names Root.nodeOffsets world machine key cidr pid base)
    (related : Corresponds names Root.nodeOffsets machine.data.dmem d)
    (pending : NodeInit.Pending names machine.data d key cidr pid base memory)
    (parentNamed : (parentId,parentBase) ∈ names.trie.nodes) (bit : direction<2)
    (hasParent : d.nodes.get? parentId=some parentNode) (hasPeer : d.peers.get? pid=some owner) :
    Corresponds (names.allocated base) Root.nodeOffsets
      (connectMemory memory base (parentBase+(direction+1)*8) ((parentBase+(direction+1)*8) ||| direction))
      (childInstalled d parentId direction key cidr machine.data.regs.rbp.toNat pid parentNode owner) := by
  unfold Corresponds
  rw [target_childInstalled d parentId direction key cidr machine.data.regs.rbp.toNat pid parentNode owner
    hasParent hasPeer (target_nodes_below related)]
  exact reconstruct_child_connect fields related pending parentNamed bit

#print axioms child_connect_corresponds
end Binary.Pair.Allowedips
