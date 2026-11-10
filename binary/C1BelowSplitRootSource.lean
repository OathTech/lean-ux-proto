import C1BelowSplitRoot

/- Origin: trial source binary-trials/t5/T5RootSource.lean on branch task/binary-trials (unreviewed), ported for C1 work
package 3 with module and namespace renames only unless a comment marked "C1 port" says otherwise. -/
/-! Trial T5, stage 1, NULL-parent subcase (mirror link): the mirror's
`chooseAndConnectNode node down; chooseAndConnectNode node newnode; connectNode root node`
on the device after both allocations, and the projection of the result. -/
namespace Binary.Pair.Allowedips.C1Split
open Leanux Leanux.WG

def intermediateRootInstalled (d : Device) (v4 : Bool) (downId b1 b2 key cidr common width pid : Nat)
    (downNode : AipNode) (owner : Peer) : Device :=
  let leaf := newNode key cidr width (some pid)
  let i0 := newNode key common width none
  let i1 := {i0 with bit:=i0.bit.set! b1 (some downId)}
  let i2 := {i1 with bit:=i1.bit.set! b2 (some d.nextNode)}
  { d with
    nextNode := d.nextNode+1+1
    nodes := (((((((d.nodes.insert d.nextNode leaf).insert (d.nextNode+1) i0).insert downId
        {downNode with parent:=.child (d.nextNode+1) b1}).insert (d.nextNode+1) i1).insert d.nextNode
        {leaf with parent:=.child (d.nextNode+1) b2}).insert (d.nextNode+1) i2).insert (d.nextNode+1)
        {i2 with parent:=if v4 then Slot.root4 else Slot.root6})
    peers := d.peers.insert pid {owner with allowedipsList:=owner.allowedipsList++[d.nextNode]}
    peerAllowedips := if v4 then {d.peerAllowedips with root4:=some (d.nextNode+1)}
      else {d.peerAllowedips with root6:=some (d.nextNode+1)} }

theorem intermediate_root_run (w : WGWorld) (ambient : Ambient) (d : Device) (v4 : Bool)
    (downId b1 b2 key cidr common width pid : Nat) (downNode : AipNode) (owner : Peer)
    (hasDown : d.nodes[downId]?=some downNode) (downBelow : downId<d.nextNode)
    (proper : common<width)
    (downChoice : b1=downNode.bits/2^(width-1-common)%2)
    (leafChoice : b2=key/2^(width-1-common)%2) :
    (((do
      Leanux.WG.liftAip (Leanux.WG.chooseAndConnectNode (d.nextNode+1) downId)
      Leanux.WG.liftAip (Leanux.WG.chooseAndConnectNode (d.nextNode+1) d.nextNode)
      Leanux.WG.liftAip (Leanux.WG.connectNode (if v4 then Slot.root4 else Slot.root6) (d.nextNode+1)) :
        Leanux.WG.M Unit).run
        {w with dev:=some (intermediateAllocated d key cidr common width pid owner)}).run ambient)=
      .ok (((),{w with dev:=some (intermediateRootInstalled d v4 downId b1 b2 key cidr common
        width pid downNode owner)}),ambient) := by
  have small1 : ¬1<b1 := by omega
  have small2 : ¬1<b2 := by omega
  have f1 : d.nextNode≠downId := Ne.symm (Nat.ne_of_lt downBelow)
  have f2 : d.nextNode+1≠downId := Ne.symm (Nat.ne_of_lt (Nat.lt_succ_of_lt downBelow))
  cases v4 <;>
  simp [Leanux.WG.chooseAndConnectNode,Leanux.WG.choose,Leanux.WG.getDev,
    Leanux.WG.modifyDev,Leanux.WG.connectNode,Leanux.WG.liftAip,Leanux.WG.getNode,
    Leanux.WG.setNode,Leanux.WG.slotSet,hasDown,Std.TreeMap.getElem?_insert,Std.TreeMap.getElem_insert,
    f1,f2,Ne.symm f1,Ne.symm f2,
    intermediateRootInstalled,intermediateAllocated,newNode,←downChoice,←leafChoice,
    small1,small2,Nat.not_le.mpr proper]

#print axioms intermediate_root_run

theorem target_intermediateRootInstalled (d : Device) (v4 : Bool)
    (downId b1 b2 key cidr common width pid : Nat) (downNode : AipNode) (owner : Peer)
    (hasDown : d.nodes.get? downId=some downNode) (hasPeer : d.peers.get? pid=some owner)
    (below : ∀ pair ∈ d.nodes.toList, pair.1<d.nextNode) :
    target (intermediateRootInstalled d v4 downId b1 b2 key cidr common width pid downNode owner)=
      installedIntermediateRoot v4 downId b1 b2 key cidr common width pid (target d) := by
  have downBelow := below (downId,downNode) (Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hasDown)
  have f1 : d.nextNode≠downId := Ne.symm (Nat.ne_of_lt downBelow)
  have f2 : d.nextNode+1≠downId := Ne.symm (Nat.ne_of_lt (Nat.lt_succ_of_lt downBelow))
  let leaf : AipNode := {newNode key cidr width (some pid) with parent:=.child (d.nextNode+1) b2}
  let internal : AipNode := {newNode key common width none with
    bit:=((newNode key common width none).bit.set! b1 (some downId)).set! b2 (some d.nextNode),
    parent:=if v4 then Slot.root4 else Slot.root6}
  let lowered : AipNode := {downNode with parent:=.child (d.nextNode+1) b1}
  let grown := (d.nodes.insert d.nextNode leaf).insert (d.nextNode+1) internal
  have hasDownAfter : grown.get? downId=some downNode := by
    simpa [grown,Std.TreeMap.getElem?_insert,f1,f2] using hasDown
  have sameTree : (intermediateRootInstalled d v4 downId b1 b2 key cidr common width pid
      downNode owner).nodes.Equiv (grown.insert downId lowered) := by
    apply Std.TreeMap.Equiv.of_forall_constGet?_eq
    intro current
    by_cases atDown : downId=current
    · subst atDown
      simp [intermediateRootInstalled,grown,Std.TreeMap.getElem_insert,f1,f2,lowered,leaf,internal,newNode]
    · by_cases atInternal : d.nextNode+1=current
      · subst atInternal
        simp [intermediateRootInstalled,grown,Std.TreeMap.getElem_insert,atDown,lowered,leaf,internal,newNode]
      · by_cases atLeaf : d.nextNode=current
        · subst atLeaf
          simp [intermediateRootInstalled,grown,Std.TreeMap.getElem_insert,atDown,lowered,leaf,internal,newNode]
        · simp [intermediateRootInstalled,grown,Std.TreeMap.getElem?_insert,atDown,atInternal,atLeaf,
            lowered,leaf,internal,newNode]
  have leafList : (d.nodes.insert d.nextNode leaf).toList=d.nodes.toList++[(d.nextNode,leaf)] :=
    tree_insert_max d.nodes d.nextNode leaf below
  have grownList : grown.toList=d.nodes.toList++[(d.nextNode,leaf)]++[(d.nextNode+1,internal)] := by
    have step := tree_insert_max (d.nodes.insert d.nextNode leaf) (d.nextNode+1) internal (by
      intro pair member
      rw [leafList] at member
      rcases List.mem_append.mp member with present|fresh
      · exact Nat.lt_succ_of_lt (below pair present)
      · have equal : pair=(d.nextNode,leaf) := by simpa using fresh
        rw [equal]
        exact Nat.lt_succ_self _)
    rw [step,leafList]
  have nodes : (intermediateRootInstalled d v4 downId b1 b2 key cidr common width pid
      downNode owner).nodes.toList=
      d.nodes.toList.map (connectUpdate downId (d.nextNode+1) b1)++
      [(d.nextNode,leaf)]++[(d.nextNode+1,internal)] := by
    rw [sameTree.toList_eq,Trie.tree_insert_present _ downId downNode lowered hasDownAfter,grownList,
      List.map_append,List.map_append,List.map_cons,List.map_nil,List.map_cons,List.map_nil]
    simp only [f1,f2,ite_false]
    apply congrArg (· ++ [(d.nextNode,leaf)]++[(d.nextNode+1,internal)])
    apply List.map_congr_left
    rintro ⟨current,node⟩ member
    have found := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp member
    have less : current<d.nextNode := below _ member
    have notInternal : current≠d.nextNode+1 := Nat.ne_of_lt (Nat.lt_succ_of_lt less)
    by_cases same : current=downId
    · subst current
      have equal := Option.some.inj (found.symm.trans hasDown)
      subst node
      simp [connectUpdate,lowered]
    · simp [connectUpdate,same,notInternal]
  have peers : (intermediateRootInstalled d v4 downId b1 b2 key cidr common width pid
      downNode owner).peers.toList=
      d.peers.toList.map (fun (current,p) =>
        (current,if current=pid then {owner with allowedipsList:=owner.allowedipsList++[d.nextNode]} else p)) :=
    Trie.tree_insert_present d.peers pid owner _ hasPeer
  have peerProjection : ((intermediateRootInstalled d v4 downId b1 b2 key cidr common width pid
      downNode owner).peers.toList.map
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
  change ({table:=_,nodes:=_,peers:=_,nextNode:=d.nextNode+1+1} : State)=_
  rw [nodes,peerProjection]
  rfl

#print axioms target_intermediateRootInstalled

/-- Stage 1, NULL parent: the final memory corresponds to the mirror device after the
two connections and the root publication. -/
theorem intermediate_root_corresponds {names : Names} {machine : MachineState}
    {key cidr common pid base base2 downId downBase b1 b2 : Nat}
    {memory initialized : DataMem} {d : Device} {downNode : AipNode} {owner : Peer} (v4 : Bool)
    (related : Corresponds names Root.nodeOffsets machine.data.dmem d)
    (pending : NodeInit.Pending names machine.data d key cidr pid base memory)
    (valid2 : validate ((names.allocated base).allocated base2) Root.nodeOffsets=.ok ())
    (init : InternalInit (names.allocated base) memory initialized base2 key common
      machine.data.regs.rbp.toNat)
    (downNamed : (downId,downBase) ∈ names.trie.nodes)
    (bit1 : b1<2) (bit2 : b2<2)
    (hasDown : d.nodes.get? downId=some downNode) (hasPeer : d.peers.get? pid=some owner) :
    Corresponds ((names.allocated base).allocated base2) Root.nodeOffsets
      (connectMemory (connectMemory (connectMemory initialized
          downBase (base2+8+b1*8) ((base2+(b1+1)*8) ||| b1))
          base (base2+8+b2*8) ((base2+(b2+1)*8) ||| b2))
          base2 (names.table+rootOffset v4) ((names.table+rootOffset v4) ||| 2))
      (intermediateRootInstalled d v4 downId b1 b2 key cidr common
        machine.data.regs.rbp.toNat pid downNode owner) := by
  unfold Corresponds
  rw [target_intermediateRootInstalled d v4 downId b1 b2 key cidr common
    machine.data.regs.rbp.toNat pid downNode owner hasDown hasPeer (target_nodes_below related)]
  exact reconstruct_intermediate_root v4 related pending valid2 init downNamed bit1 bit2

#print axioms intermediate_root_corresponds
end Binary.Pair.Allowedips.C1Split
