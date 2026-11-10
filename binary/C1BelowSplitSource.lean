import C1BelowSplitRun

/- Origin: trial source binary-trials/t5/T5Source.lean on branch task/binary-trials (unreviewed), ported for C1 work
package 3 with module and namespace renames only unless a comment marked "C1 port" says otherwise. -/
namespace Binary.Pair.Allowedips.C1Split
open Leanux Leanux.WG

theorem target_intermediateInstalled (d : Device)
    (downId b1 b2 parentId direction key cidr common width pid : Nat)
    (downNode parentNode : AipNode) (owner : Peer)
    (hasDown : d.nodes.get? downId=some downNode) (hasParent : d.nodes.get? parentId=some parentNode)
    (hasPeer : d.peers.get? pid=some owner) (different : downId≠parentId)
    (below : ∀ pair ∈ d.nodes.toList, pair.1<d.nextNode) :
    target (intermediateInstalled d downId b1 b2 parentId direction key cidr common width pid
      downNode parentNode owner)=
      installedIntermediate downId b1 b2 parentId direction key cidr common width pid (target d) := by
  have downBelow := below (downId,downNode) (Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hasDown)
  have parentBelow := below (parentId,parentNode) (Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hasParent)
  have f1 : d.nextNode≠downId := Ne.symm (Nat.ne_of_lt downBelow)
  have f2 : d.nextNode+1≠downId := Ne.symm (Nat.ne_of_lt (Nat.lt_succ_of_lt downBelow))
  have f3 : d.nextNode≠parentId := Ne.symm (Nat.ne_of_lt parentBelow)
  have f4 : d.nextNode+1≠parentId := Ne.symm (Nat.ne_of_lt (Nat.lt_succ_of_lt parentBelow))
  let leaf : AipNode := {newNode key cidr width (some pid) with parent:=.child (d.nextNode+1) b2}
  let internal : AipNode := {newNode key common width none with
    bit:=((newNode key common width none).bit.set! b1 (some downId)).set! b2 (some d.nextNode),
    parent:=.child parentId direction}
  let lowered : AipNode := {downNode with parent:=.child (d.nextNode+1) b1}
  let updated : AipNode := {parentNode with bit:=parentNode.bit.set! direction (some (d.nextNode+1))}
  let grown := (d.nodes.insert d.nextNode leaf).insert (d.nextNode+1) internal
  have hasDownAfter : grown.get? downId=some downNode := by
    simpa [grown,Std.TreeMap.getElem?_insert,f1,f2] using hasDown
  have hasParentAfter : (grown.insert downId lowered).get? parentId=some parentNode := by
    simpa [grown,Std.TreeMap.getElem?_insert,f3,f4,different] using hasParent
  have sameTree : (intermediateInstalled d downId b1 b2 parentId direction key cidr common width pid
      downNode parentNode owner).nodes.Equiv ((grown.insert downId lowered).insert parentId updated) := by
    apply Std.TreeMap.Equiv.of_forall_constGet?_eq
    intro current
    by_cases atParent : parentId=current
    · subst atParent
      simp [intermediateInstalled,grown,updated,lowered,leaf,internal,newNode]
    · by_cases atDown : downId=current
      · subst atDown
        simp [intermediateInstalled,grown,Std.TreeMap.getElem_insert,
          atParent,f1,f2,updated,lowered,leaf,internal,newNode]
      · by_cases atInternal : d.nextNode+1=current
        · subst atInternal
          simp [intermediateInstalled,grown,Std.TreeMap.getElem_insert,
            atParent,atDown,updated,lowered,leaf,internal,newNode]
        · by_cases atLeaf : d.nextNode=current
          · subst atLeaf
            simp [intermediateInstalled,grown,Std.TreeMap.getElem_insert,
              atParent,atDown,updated,lowered,leaf,internal,newNode]
          · simp [intermediateInstalled,grown,Std.TreeMap.getElem?_insert,
              atParent,atDown,atInternal,atLeaf,updated,lowered,leaf,internal,newNode]
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
  have nodes : (intermediateInstalled d downId b1 b2 parentId direction key cidr common width pid
      downNode parentNode owner).nodes.toList=
      d.nodes.toList.map (fun e =>
        connectUpdate (d.nextNode+1) parentId direction (connectUpdate downId (d.nextNode+1) b1 e))++
      [(d.nextNode,leaf)]++[(d.nextNode+1,internal)] := by
    rw [sameTree.toList_eq,Trie.tree_insert_present _ parentId parentNode updated hasParentAfter,
      Trie.tree_insert_present _ downId downNode lowered hasDownAfter,grownList,
      List.map_append,List.map_append,List.map_append,List.map_append,
      List.map_cons,List.map_nil,List.map_cons,List.map_nil,List.map_cons,List.map_nil,
      List.map_cons,List.map_nil,List.map_map]
    simp only [f1,f2,f3,f4,ite_false]
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
      simp [connectUpdate,lowered,different,notInternal]
    · by_cases parentSame : current=parentId
      · subst current
        have equal := Option.some.inj (found.symm.trans hasParent)
        subst node
        simp [connectUpdate,updated,same,notInternal]
      · simp [connectUpdate,same,parentSame,notInternal]
  have peers : (intermediateInstalled d downId b1 b2 parentId direction key cidr common width pid
      downNode parentNode owner).peers.toList=
      d.peers.toList.map (fun (current,p) =>
        (current,if current=pid then {owner with allowedipsList:=owner.allowedipsList++[d.nextNode]} else p)) :=
    Trie.tree_insert_present d.peers pid owner _ hasPeer
  have peerProjection : ((intermediateInstalled d downId b1 b2 parentId direction key cidr common width pid
      downNode parentNode owner).peers.toList.map
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
  change ({table:=d.peerAllowedips,nodes:=_,peers:=_,nextNode:=d.nextNode+1+1} : State)=_
  rw [nodes,peerProjection]
  rfl

#print axioms target_intermediateInstalled

/-- Stage 1: the memory after the internal node's initialization and the six
connection stores corresponds, under the twice-extended names, to the mirror device
after the three `chooseAndConnectNode` calls of the intermediate case. -/
theorem intermediate_connect_corresponds {names : Names} {machine : MachineState}
    {key cidr common pid base base2 downId downBase parentId parentBase b1 b2 direction : Nat}
    {memory initialized : DataMem} {d : Device} {downNode parentNode : AipNode} {owner : Peer}
    (related : Corresponds names Root.nodeOffsets machine.data.dmem d)
    (pending : NodeInit.Pending names machine.data d key cidr pid base memory)
    (valid2 : validate ((names.allocated base).allocated base2) Root.nodeOffsets=.ok ())
    (init : InternalInit (names.allocated base) memory initialized base2 key common
      machine.data.regs.rbp.toNat)
    (downNamed : (downId,downBase) ∈ names.trie.nodes)
    (parentNamed : (parentId,parentBase) ∈ names.trie.nodes)
    (bit1 : b1<2) (bit2 : b2<2) (bit : direction<2)
    (hasDown : d.nodes.get? downId=some downNode) (hasParent : d.nodes.get? parentId=some parentNode)
    (hasPeer : d.peers.get? pid=some owner)
    -- `down` hangs below `parent` in a tree (`down = parent->bit[...]`), so they differ.
    (different : downId≠parentId) :
    Corresponds ((names.allocated base).allocated base2) Root.nodeOffsets
      (connectMemory (connectMemory (connectMemory initialized
          downBase (base2+8+b1*8) ((base2+(b1+1)*8) ||| b1))
          base (base2+8+b2*8) ((base2+(b2+1)*8) ||| b2))
          base2 (parentBase+8+direction*8) ((parentBase+(direction+1)*8) ||| direction))
      (intermediateInstalled d downId b1 b2 parentId direction key cidr common
        machine.data.regs.rbp.toNat pid downNode parentNode owner) := by
  unfold Corresponds
  rw [target_intermediateInstalled d downId b1 b2 parentId direction key cidr common
    machine.data.regs.rbp.toNat pid downNode parentNode owner hasDown hasParent hasPeer different
    (target_nodes_below related)]
  exact reconstruct_intermediate_connect related pending valid2 init downNamed parentNamed bit1 bit2 bit

#print axioms intermediate_connect_corresponds
end Binary.Pair.Allowedips.C1Split
