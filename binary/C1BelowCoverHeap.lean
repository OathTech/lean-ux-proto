import C1BelowCoverIncoming

/-! Origin: trial T2, `binary-trials/t2/CoverHeap.lean` on `task/binary-trials` (unreviewed), copied
under the package prefix with the namespaces suffixed `C1Cover`; proofs unchanged. -/

/-! Trial T2, part 3c: the structural assertion `heap` is restored by the
covering insertion. -/
namespace Binary.Pair.Allowedips.C1Cover
open Leanux Leanux.WG Root

/-- The fresh record of the covering case, as it appears in `installedCover`. -/
abbrev coverLeaf (downId b parentId direction key cidr width pid : Nat) : AipNode :=
  {newNode key cidr width (some pid) with
    bit:=(newNode key cidr width (some pid)).bit.set! b (some downId),
    parent:=.child parentId direction}

theorem coverUpdate_peer (downId b parentId direction fresh : Nat) (entry : NodeId×AipNode) :
    (coverUpdate downId b parentId direction fresh entry).2.peer=entry.2.peer := by
  rcases entry with ⟨current,node⟩
  by_cases p : current=parentId
  · subst p
    by_cases q : current=downId
    · subst q
      simp [coverUpdate,reparent,installChild]
    · simp [coverUpdate,reparent,installChild,q]
  · by_cases q : current=downId
    · subst q
      simp [coverUpdate,reparent,installChild,p]
    · simp [coverUpdate,reparent,installChild,p,q]

theorem trieState_installedCover (s : State) (downId b parentId direction key cidr width pid : Nat) :
    trieState (installedCover downId b parentId direction key cidr width pid s)=
      Trie.attachedChild (trieState s) parentId direction s.nextNode
        (Trie.targetNode (coverLeaf downId b parentId direction key cidr width pid)) := by
  simp only [trieState,installedCover,Trie.attachedChild,List.map_append,List.map_cons,List.map_nil,
    List.map_map,Function.comp_def,appendOwner]
  congr 1
  congr 1
  apply List.map_congr_left
  rintro ⟨current,node⟩ _
  by_cases p : current=parentId
  · subst p
    by_cases q : current=downId
    · subst q
      simp [coverUpdate,reparent,installChild,Trie.changeChild,Trie.targetNode]
    · simp [coverUpdate,reparent,installChild,Trie.changeChild,Trie.targetNode,q]
  · by_cases q : current=downId
    · subst q
      simp [coverUpdate,reparent,installChild,Trie.changeChild,Trie.targetNode,p]
    · simp [coverUpdate,reparent,installChild,Trie.changeChild,Trie.targetNode,p,q]

theorem coverLeaf_absent {id downId b parentId direction key cidr width pid : Nat}
    (downBit : b<2) (notDown : id≠downId) :
    some id ∉ (coverLeaf downId b parentId direction key cidr width pid).bit.toList := by
  have which : b=0 ∨ b=1 := by omega
  rcases which with rfl|rfl <;> simp [newNode,notDown]

theorem incomingStep_coverLeaf {fresh downId b parentId direction key cidr width pid : Nat}
    (downBit : b<2) (before : List Slot) :
    incomingStep downId (fresh,coverLeaf downId b parentId direction key cidr width pid) before=
      .ok (.yield (.child fresh b::before)) := by
  have which : b=0 ∨ b=1 := by omega
  rcases which with rfl|rfl
  · simp [incomingStep,newNode]
    rfl
  · simp [incomingStep,newNode]
    rfl

theorem structureCheck_installedCover_old {s : State}
    {downId b parentId direction key cidr width pid id : Nat}
    {parentNode node : AipNode} {left right : Option Nat}
    (unique : (s.nodes.map Prod.fst).Nodup) (parent : (parentId,parentNode) ∈ s.nodes)
    (shape : parentNode.bit=#[left,right]) (bit : direction<2) (downBit : b<2)
    (occupied : parentNode.bit[direction]?=some (some downId))
    (different : id≠s.nextNode) (notDown : id≠downId) :
    structureCheck (installedCover downId b parentId direction key cidr width pid s) id
        (coverUpdate downId b parentId direction s.nextNode (id,node)).2=structureCheck s id node := by
  have metadata (state : State) : structureCheck state id
      (coverUpdate downId b parentId direction s.nextNode (id,node)).2=structureCheck state id node := by
    by_cases same : id=parentId
    · simp only [coverUpdate,reparent,installChild,ite_eq_right notDown,ite_eq_left same]; rfl
    · simp only [coverUpdate,reparent,installChild,ite_eq_right notDown,ite_eq_right same]
  rw [metadata,structureCheck_walk,structureCheck_walk]
  have children (before : List Slot) :
      forIn (installedCover downId b parentId direction key cidr width pid s).nodes before (incomingStep id)=
        forIn s.nodes before (incomingStep id) := by
    change forIn ((s.nodes.map (coverUpdate downId b parentId direction s.nextNode))++
      [(s.nextNode,coverLeaf downId b parentId direction key cidr width pid)]) before (incomingStep id)=_
    rw [forIn_append_identity (fun pair member current => by
      obtain rfl := List.mem_singleton.mp member
      exact incomingStep_absent id _ (coverLeaf_absent downBit notDown) current)]
    rw [List.forIn_map]
    apply forIn_congr_mem
    rintro ⟨current,original⟩ present initial
    change incomingStep id (coverUpdate downId b parentId direction s.nextNode (current,original)) initial=
      incomingStep id (current,original) initial
    rw [incomingStep_cover]
    by_cases same : current=parentId
    · subst current
      have parentEq : original=parentNode := congrArg Prod.snd
        (Option.some.inj ((Trie.find_node_key unique present).symm.trans (Trie.find_node_key unique parent)))
      subst original
      exact incomingStep_replace_old shape bit occupied different notDown initial
    · simp only [installChild,ite_eq_right same]
  simp only [show (installedCover downId b parentId direction key cidr width pid s).table=s.table from rfl]
  congr 1
  funext incoming
  rw [children]

#print axioms structureCheck_installedCover_old

theorem structureCheck_installedCover_down {s : State} {names memory}
    (b key cidr width pid : Nat) {downId parentId direction : Nat}
    {parentNode downNode : AipNode} {left right : Option Nat}
    (checked : heap names s memory=.ok ()) (below : ∀ entry ∈ s.nodes, entry.1<s.nextNode)
    (unique : (s.nodes.map Prod.fst).Nodup) (parent : (parentId,parentNode) ∈ s.nodes)
    (down : (downId,downNode) ∈ s.nodes)
    (shape : parentNode.bit=#[left,right]) (bit : direction<2) (downBit : b<2)
    (occupied : parentNode.bit[direction]?=some (some downId)) :
    structureCheck (installedCover downId b parentId direction key cidr width pid s) downId
      (coverUpdate downId b parentId direction s.nextNode (downId,downNode)).2=.ok () := by
  have tree := ((heap_checks names s memory).mp checked).1
  change Trie.heap (trieState s) _=_ at tree
  have trieParent : (parentId,Trie.targetNode parentNode) ∈ (trieState s).nodes :=
    List.mem_map.mpr ⟨(parentId,parentNode),parent,rfl⟩
  have trieShape : (Trie.targetNode parentNode).children=#[left,right] := shape
  have trieOccupied : (Trie.targetNode parentNode).children[direction]?=some (some downId) := occupied
  have downEdge : (some downId,direction) ∈ (Trie.targetNode parentNode).children.toList.zipIdx := by
    apply List.mk_mem_zipIdx_iff_getElem?.mpr
    simpa using trieOccupied
  obtain ⟨_,_,notRoot,_⟩ := Trie.heap_edge_facts tree parentId _ trieParent _ downEdge downId rfl
  have other4 : s.table.root4≠some downId := fun equal => notRoot (by simp [equal])
  have other6 : s.table.root6≠some downId := fun equal => notRoot (by simp [equal])
  obtain ⟨elsewhere,rightNe,leftNe⟩ := Trie.C1Cover.heap_occupant_unique tree trieParent trieShape bit trieOccupied
  have freshNe : s.nextNode≠downId := Ne.symm (Nat.ne_of_lt (below _ down))
  have absentAll : ∀ entry ∈ s.nodes,
      some downId ∉ (installChild parentId direction s.nextNode entry).2.bit.toList := by
    rintro ⟨current,original⟩ present
    by_cases same : current=parentId
    · subst current
      have parentEq : original=parentNode := congrArg Prod.snd
        (Option.some.inj ((Trie.find_node_key unique present).symm.trans (Trie.find_node_key unique parent)))
      subst original
      have which : direction=0 ∨ direction=1 := by omega
      rcases which with rfl|rfl
      · have otherNe := rightNe rfl
        simp [installChild,shape,Ne.symm freshNe,Ne.symm otherNe]
      · have otherNe := leftNe rfl
        simp [installChild,shape,Ne.symm freshNe,Ne.symm otherNe]
    · simp only [installChild,ite_eq_right same]
      exact elsewhere (current,Trie.targetNode original) (List.mem_map.mpr ⟨(current,original),present,rfl⟩)
        (fun equal => same (congrArg Prod.fst equal))
  have walk : forIn (installedCover downId b parentId direction key cidr width pid s).nodes []
      (incomingStep downId)=.ok [Slot.child s.nextNode b] := by
    change forIn ((s.nodes.map (coverUpdate downId b parentId direction s.nextNode))++
      [(s.nextNode,coverLeaf downId b parentId direction key cidr width pid)]) [] (incomingStep downId)=_
    have steps : ∀ pair ∈ s.nodes.map (coverUpdate downId b parentId direction s.nextNode), ∀ current,
        incomingStep downId pair current=.ok (.yield current) := by
      intro pair member current
      obtain ⟨entry,atEntry,rfl⟩ := List.mem_map.mp member
      rw [incomingStep_cover]
      exact incomingStep_absent downId _ (absentAll entry atEntry) current
    rw [forIn_append_yield (fun pair member before after run =>
      ⟨before,(Except.ok.inj ((steps pair member before).symm.trans run)).symm⟩) (forIn_identity steps [])]
    rw [List.forIn_cons,incomingStep_coverLeaf downBit]
    rfl
  have parentEq : (coverUpdate downId b parentId direction s.nextNode (downId,downNode)).2.parent=
      .child s.nextNode b := by
    by_cases same : downId=parentId
    · subst same
      simp [coverUpdate,reparent,installChild]
    · simp [coverUpdate,reparent,installChild,same]
  exact structureCheck_single other4 other6 walk parentEq

#print axioms structureCheck_installedCover_down

theorem structureCheck_installedCover_new {s : State} {names memory}
    (b key cidr width pid : Nat) {downId parentId direction : Nat}
    {parentNode downNode : AipNode} {left right : Option Nat}
    (checked : heap names s memory=.ok ()) (below : ∀ entry ∈ s.nodes, entry.1<s.nextNode)
    (unique : (s.nodes.map Prod.fst).Nodup) (parent : (parentId,parentNode) ∈ s.nodes)
    (down : (downId,downNode) ∈ s.nodes)
    (shape : parentNode.bit=#[left,right]) (bit : direction<2) (downBit : b<2) :
    structureCheck (installedCover downId b parentId direction key cidr width pid s) s.nextNode
      (coverLeaf downId b parentId direction key cidr width pid)=.ok () := by
  have other4 : s.table.root4≠some s.nextNode := by
    intro equal
    have bound : s.nextNode<s.nextNode := roots_below checked below s.nextNode (by simp [equal])
    omega
  have other6 : s.table.root6≠some s.nextNode := by
    intro equal
    have bound : s.nextNode<s.nextNode := roots_below checked below s.nextNode (by simp [equal])
    omega
  have absent : ∀ entry ∈ s.nodes, some s.nextNode ∉ entry.2.bit.toList := by
    rintro ⟨id,node⟩ member child
    have bound : s.nextNode<s.nextNode := edges_below checked below id node member s.nextNode child
    omega
  have freshNe : s.nextNode≠downId := Ne.symm (Nat.ne_of_lt (below _ down))
  have walk : forIn (installedCover downId b parentId direction key cidr width pid s).nodes []
      (incomingStep s.nextNode)=.ok [Slot.child parentId direction] := by
    change forIn ((s.nodes.map (coverUpdate downId b parentId direction s.nextNode))++
      [(s.nextNode,coverLeaf downId b parentId direction key cidr width pid)]) [] (incomingStep s.nextNode)=_
    rw [forIn_append_identity (fun pair member current => by
      obtain rfl := List.mem_singleton.mp member
      exact incomingStep_absent s.nextNode _ (coverLeaf_absent downBit freshNe) current)]
    exact incoming_cover_walk unique parent shape bit absent []
  exact structureCheck_single other4 other6 walk rfl

#print axioms structureCheck_installedCover_new

theorem ownership_installedCover {names newNames o before after d}
    (downId b parentId direction key cidr width pid : Nat) (owner : Peer)
    (related : Corresponds names o before d) (shape : heap names (target d) before=.ok ())
    (hasPeer : d.peers.get? pid=some owner)
    (internal : ∀ current node, (current,node) ∈ (target d).nodes → node.peer=none →
      internalListCheck newNames after current=.ok ()) :
    ∀ id node, (id,node) ∈ (installedCover downId b parentId direction key cidr width pid (target d)).nodes →
      ownershipCheck newNames (installedCover downId b parentId direction key cidr width pid (target d))
        after id node=.ok () := by
  intro id node member
  rcases List.mem_append.mp member with old | new
  · obtain ⟨⟨current,original⟩,present,equal⟩ := List.mem_map.mp old
    have identity : current=id := congrArg Prod.fst equal
    subst current
    have peerSame : node.peer=original.peer :=
      (congrArg (fun pair : NodeId×AipNode => pair.2.peer) equal).symm.trans
        (coverUpdate_peer downId b parentId direction (target d).nextNode (id,original))
    apply ownershipCheck_of
    · rw [peerSame]
      exact (owners_installed_other (target d) true key cidr pid id
        (Nat.ne_of_lt (target_nodes_below related (id,original) present))).trans
        (heap_ownership shape id original present).1
    · rw [peerSame]
      exact internal id original present
  · obtain equal := List.mem_singleton.mp new
    cases equal
    apply ownershipCheck_of
    · exact owners_installed_new related true key cidr pid owner hasPeer
    · simp [newNode]

#print axioms ownership_installedCover

/-- Both connections' stores leave every old internal node's list head intact. -/
theorem pending_internal_covered {names : Names} {before : MachineData} {d : Device}
    {key cidr pid base downId downBase parentId parentBase b direction packed packedParent : Nat}
    {memory : DataMem}
    (pending : NodeInit.Pending names before d key cidr pid base memory)
    (g : Geometry (names.allocated base) nodeOffsets)
    (downNamed : (downId,downBase) ∈ names.trie.nodes)
    (parentNamed : (parentId,parentBase) ∈ names.trie.nodes) (downBit : b<2) (bit : direction<2) :
    ∀ current node, (current,node) ∈ (target d).nodes → node.peer=none →
      internalListCheck (names.allocated base)
        (connectMemory (connectMemory memory downBase (base+8+b*8) packed)
          base (parentBase+8+direction*8) packedParent) current=.ok () := by
  intro current node member internal
  have first := connect_frame memory downBase (base+8+b*8) packed
  have firstApart := connect_lists_apart g (List.mem_append_left _ downNamed) (allocated_node names base) downBit
  have second := connect_frame (connectMemory memory downBase (base+8+b*8) packed)
    base (parentBase+8+direction*8) packedParent
  have secondApart := connect_lists_apart g (allocated_node names base) (List.mem_append_left _ parentNamed) bit
  exact (internal_list_frame (names.allocated base) second secondApart current) ▸
    (internal_list_frame (names.allocated base) first firstApart current) ▸
    pending.internal current node member internal

#print axioms pending_internal_covered

/-- All parts of the executable allowed-IPs heap assertion are restored by the
covering insertion with a non-NULL parent. -/
theorem heap_installedCover {names newNames o before after d}
    {downId b parentId direction key cidr width pid : Nat} {parentNode downNode : AipNode} (owner : Peer)
    (related : Corresponds names o before d) (checked : heap names (target d) before=.ok ())
    (hasPeer : d.peers.get? pid=some owner)
    (parent : (parentId,parentNode) ∈ (target d).nodes) (down : (downId,downNode) ∈ (target d).nodes)
    (bit : direction<2) (downBit : b<2)
    -- `down = parent->bit[choose(parent,key)]`, found non-NULL.
    (occupied : parentNode.bit[direction]?=some (some downId))
    -- the walk matched `parent` (same family, shorter prefix of `key`, not exact).
    (sameWidth : width=parentNode.bitlen) (measure : parentNode.cidr<cidr)
    (prefixEq : key/2^(parentNode.bitlen-parentNode.cidr)=parentNode.bits/2^(parentNode.bitlen-parentNode.cidr))
    (side : key/2^(parentNode.bitlen-1-parentNode.cidr)%2=direction)
    -- the covering condition `newnode->cidr == min(cidr, common_bits(down,key,bits))`,
    -- with the walk having stopped above `down`.
    (downMeasure : cidr<downNode.cidr)
    (downPrefix : downNode.bits/2^(width-cidr)=key/2^(width-cidr))
    -- `b = choose(newnode, down->bits)`.
    (downSide : downNode.bits/2^(width-1-cidr)%2=b)
    (internal : ∀ current node, (current,node) ∈ (target d).nodes → node.peer=none →
      internalListCheck newNames after current=.ok ()) :
    heap newNames (installedCover downId b parentId direction key cidr width pid (target d)) after=.ok () := by
  have below := target_nodes_below related
  have unique := target_node_unique d
  have checks := (heap_checks names (target d) before).mp checked
  obtain ⟨base,_,read⟩ := (reconstruct_fields related).node parent
  obtain ⟨left,right,_,_,shape,_⟩ := (Trie.decodeNode_fields (decodeNode_fields read).2).children
  change parentNode.bit=#[left,right] at shape
  apply (heap_checks newNames _ after).mpr
  constructor
  · change Trie.heap (trieState (installedCover downId b parentId direction key cidr width pid (target d))) _=_
    rw [trieState_installedCover]
    apply Trie.C1Cover.heap_spliced_child
      (leaf:=Trie.targetNode (coverLeaf downId b parentId direction key cidr width pid))
      (downNode:=Trie.targetNode downNode) checks.1
      (by simpa only [trieState,List.map_map,Function.comp_def] using unique)
      (fun entry member => by
        obtain ⟨old,present,equal⟩ := List.mem_map.mp member
        exact (congrArg Prod.fst equal) ▸ Nat.ne_of_lt (below old present))
      (List.mem_map.mpr ⟨(parentId,parentNode),parent,rfl⟩)
      (List.mem_map.mpr ⟨(downId,downNode),down,rfl⟩) shape bit occupied downBit rfl
      sameWidth measure prefixEq side downMeasure downPrefix downSide
  · intro id node member
    refine ⟨?_,ownership_installedCover downId b parentId direction key cidr width pid owner related checked
      hasPeer internal id node member⟩
    rcases List.mem_append.mp member with old | new
    · obtain ⟨⟨current,original⟩,present,equal⟩ := List.mem_map.mp old
      cases equal
      by_cases isDown : current=downId
      · subst current
        have downEq : original=downNode := congrArg Prod.snd
          (Option.some.inj ((Trie.find_node_key unique present).symm.trans (Trie.find_node_key unique down)))
        subst original
        exact structureCheck_installedCover_down b key cidr width pid checked below unique parent down
          shape bit downBit occupied
      · exact (structureCheck_installedCover_old unique parent shape bit downBit occupied
          (Nat.ne_of_lt (below (current,original) present)) isDown).trans (checks.2 current original present).1
    · obtain equal := List.mem_singleton.mp new
      cases equal
      exact structureCheck_installedCover_new b key cidr width pid checked below unique parent down
        shape bit downBit

#print axioms heap_installedCover

/-- The structural assertion on the memory after the four connection stores,
from the same pending resources the reconstruction lemma uses. -/
theorem cover_connect_heap {names : Names} {world : World} {machine : MachineState}
    {key cidr pid base downId downBase parentId parentBase b direction : Nat} {memory : DataMem} {d : Device}
    {parentNode downNode : AipNode} (owner : Peer)
    (fields : NodeInit.BoundaryFields names nodeOffsets world machine key cidr pid base)
    (related : Corresponds names nodeOffsets machine.data.dmem d)
    (checked : heap names (target d) machine.data.dmem=.ok ())
    (pending : NodeInit.Pending names machine.data d key cidr pid base memory)
    (downNamed : (downId,downBase) ∈ names.trie.nodes)
    (parentNamed : (parentId,parentBase) ∈ names.trie.nodes)
    (hasPeer : d.peers.get? pid=some owner)
    (parent : (parentId,parentNode) ∈ (target d).nodes) (down : (downId,downNode) ∈ (target d).nodes)
    (bit : direction<2) (downBit : b<2)
    (occupied : parentNode.bit[direction]?=some (some downId))
    (sameWidth : machine.data.regs.rbp.toNat=parentNode.bitlen) (measure : parentNode.cidr<cidr)
    (prefixEq : key/2^(parentNode.bitlen-parentNode.cidr)=parentNode.bits/2^(parentNode.bitlen-parentNode.cidr))
    (side : key/2^(parentNode.bitlen-1-parentNode.cidr)%2=direction)
    (downMeasure : cidr<downNode.cidr)
    (downPrefix : downNode.bits/2^(machine.data.regs.rbp.toNat-cidr)=key/2^(machine.data.regs.rbp.toNat-cidr))
    (downSide : downNode.bits/2^(machine.data.regs.rbp.toNat-1-cidr)%2=b) :
    heap (names.allocated base)
      (installedCover downId b parentId direction key cidr machine.data.regs.rbp.toNat pid (target d))
      (connectMemory (connectMemory memory downBase (base+8+b*8) ((base+8+b*8) ||| b))
        base (parentBase+8+direction*8) ((parentBase+8+direction*8) ||| direction))=.ok () :=
  heap_installedCover owner related checked hasPeer parent down bit downBit occupied sameWidth measure
    prefixEq side downMeasure downPrefix downSide
    (pending_internal_covered pending (fields.geometry related) downNamed parentNamed downBit bit)

#print axioms cover_connect_heap
end Binary.Pair.Allowedips.C1Cover
