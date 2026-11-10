import C1BelowCoverRoot
import C1BelowCoverHeap

/-! Result C1, work package 3, covering path at the root: the structural
check after the fresh node replaces the family's root `down` and takes it as
its only child. Adapted from the split path's root variant
(`C1Split.heap_root_spliced`, `heap_installedIntermediateRoot`), with one
fresh node instead of two. -/
namespace Binary.Pair.Trie.C1Cover
open Leanux Leanux.WG

/-- A fresh node becomes a root in place of `down`, with `down` as its only child. -/
theorem heap_root_covered {s : State} {roots roots' : List (Option NodeId)}
    {freshId downId b : Nat} {downNode fresh : Node}
    (checked : heap s roots=.ok ()) (unique : (s.nodes.map Prod.fst).Nodup)
    (absent : ∀ entry ∈ s.nodes, entry.1≠freshId)
    (down : (downId,downNode) ∈ s.nodes) (downRoot : some downId ∈ roots)
    (rootsNew : ∀ r ∈ roots', r=some freshId ∨ (r ∈ roots ∧ r≠some downId))
    (bit : b<2)
    (freshChildren : fresh.children=(#[none,none] : Array (Option NodeId)).set! b (some downId))
    (downWidth : downNode.width=fresh.width) (downMeasure : fresh.cidr<downNode.cidr)
    (downPrefix : downNode.key/2^(fresh.width-fresh.cidr)=fresh.key/2^(fresh.width-fresh.cidr))
    (downSide : downNode.key/2^(fresh.width-1-fresh.cidr)%2=b) :
    heap {s with nodes:=s.nodes++[(freshId,fresh)]} roots'=.ok () := by
  have downFound := find_node_key unique down
  have rootOld : ∀ next, some next ∈ roots' → next=freshId ∨ (some next ∈ roots ∧ next≠downId) := by
    intro next member
    rcases rootsNew _ member with equal | ⟨old,ne⟩
    · exact .inl (Option.some.inj equal)
    · exact .inr ⟨old,fun same => ne (congrArg some same)⟩
  have findOld {next : Nat} {child : Node} (found : s.nodes.find? (·.1==next)=some (next,child)) :
      (s.nodes++[(freshId,fresh)]).find? (·.1==next)=some (next,child) := by
    simp only [List.find?_append,found,Option.some_or]
  have which : b=0 ∨ b=1 := by omega
  apply heap_of_facts
  · intro id member
    rcases rootOld id member with rfl | ⟨old,_⟩
    · exact ⟨fresh,List.mem_append_right _ (List.mem_singleton_self _)⟩
    · obtain ⟨node,present⟩ := heap_root checked old
      exact ⟨node,List.mem_append_left _ present⟩
  · intro id node member
    rcases List.mem_append.mp member with present | last
    · intro edge atEdge next equal
      obtain ⟨child,found,notRoot,rest⟩ := heap_edge_facts checked id node present edge atEdge next equal
      refine ⟨child,findOld found,?_,rest⟩
      intro member
      rcases rootOld next member with same | ⟨old,_⟩
      · exact absent (next,child) (List.mem_of_find?_eq_some found) same
      · exact notRoot old
    · obtain equal := List.mem_singleton.mp last
      cases equal
      have downEdge : EdgeFacts {s with nodes:=s.nodes++[(freshId,fresh)]} roots' fresh (some downId,b) := by
        intro next equal
        cases Option.some.inj equal
        refine ⟨downNode,findOld downFound,?_,downWidth,downMeasure,downPrefix,downSide⟩
        intro member
        rcases rootOld downId member with same | ⟨_,ne⟩
        · exact absent _ down same
        · exact ne rfl
      intro edge atEdge
      rw [freshChildren] at atEdge
      rcases which with rfl|rfl
      · have cases : edge=(some downId,0) ∨ edge=(none,1) := by simpa using atEdge
        rcases cases with rfl|rfl
        · exact downEdge
        · intro next equal; cases equal
      · have cases : edge=(none,0) ∨ edge=(some downId,1) := by simpa using atEdge
        rcases cases with rfl|rfl
        · intro next equal; cases equal
        · exact downEdge
  · have oldNodup := heap_children_nodup checked
    have downNotChild : downId ∉ s.nodes.flatMap nodeChildren := by
      intro member
      obtain ⟨⟨id,node⟩,atNode,atChildren⟩ := List.mem_flatMap.mp member
      obtain ⟨edge,atEdge,atChild⟩ := List.mem_flatMap.mp atChildren
      have equal : edge.1=some downId := by simpa [edgeChildren] using atChild
      obtain ⟨_,_,notRoot,_⟩ := heap_edge_facts checked id node atNode edge atEdge downId equal
      exact notRoot downRoot
    have freshList : nodeChildren (freshId,fresh)=[downId] := by
      rcases which with rfl|rfl <;> simp [nodeChildren,freshChildren,edgeChildren]
    simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,freshList,List.append_nil]
    exact List.nodup_append.mpr ⟨oldNodup,by simp,fun a member b atNew equal => by
      have : b=downId := by simpa using atNew
      exact downNotChild (this ▸ equal ▸ member)⟩

#print axioms heap_root_covered
end Binary.Pair.Trie.C1Cover

namespace Binary.Pair.Allowedips.C1Cover
open Leanux Leanux.WG Root

/-- The fresh node as the root of its family, above `down`. -/
abbrev coverRootLeaf (v4 : Bool) (downId b key cidr width pid : Nat) : AipNode :=
  {newNode key cidr width (some pid) with
    bit:=(newNode key cidr width (some pid)).bit.set! b (some downId),
    parent:=if v4 then Slot.root4 else Slot.root6}

theorem incomingStep_same (id : Nat) {a b : NodeId×AipNode} (key : a.1=b.1) (bits : a.2.bit=b.2.bit)
    (before : List Slot) : incomingStep id a before=incomingStep id b before := by
  unfold incomingStep
  rw [key,bits]

theorem reparent_bit (downId : Nat) (slot : Slot) (entry : NodeId×AipNode) :
    (reparent downId slot entry).2.bit=entry.2.bit := by
  unfold reparent
  split <;> rfl

theorem reparent_peer (downId : Nat) (slot : Slot) (entry : NodeId×AipNode) :
    (reparent downId slot entry).2.peer=entry.2.peer := by
  unfold reparent
  split <;> rfl

theorem coverRootLeaf_absent {v4 : Bool} {id downId b key cidr width pid : Nat}
    (downBit : b<2) (notDown : id≠downId) :
    some id ∉ (coverRootLeaf v4 downId b key cidr width pid).bit.toList := by
  have which : b=0 ∨ b=1 := by omega
  rcases which with rfl|rfl <;> simp [newNode,notDown]

theorem incomingStep_coverRootLeaf {v4 : Bool} {fresh downId b key cidr width pid : Nat}
    (downBit : b<2) (before : List Slot) :
    incomingStep downId (fresh,coverRootLeaf v4 downId b key cidr width pid) before=
      .ok (.yield (.child fresh b::before)) := by
  have which : b=0 ∨ b=1 := by omega
  rcases which with rfl|rfl
  · simp [incomingStep,newNode]
    rfl
  · simp [incomingStep,newNode]
    rfl

/-- `heap` after the covering insertion at the root of a family. -/
theorem heap_installedCoverRoot {names newNames o before after d} (v4 : Bool)
    {downId b key cidr width pid : Nat} {downNode : AipNode} (owner : Peer)
    (related : Corresponds names o before d) (checked : heap names (target d) before=.ok ())
    (hasPeer : d.peers.get? pid=some owner)
    (down : (downId,downNode) ∈ (target d).nodes) (bit : b<2)
    (rootHere : (if v4 then (target d).table.root4 else (target d).table.root6)=some downId)
    (otherRoot : (if v4 then (target d).table.root6 else (target d).table.root4)≠some downId)
    (family : width=if v4 then 32 else 128) (downWidth : downNode.bitlen=width)
    (downMeasure : cidr<downNode.cidr)
    (downPrefix : downNode.bits/2^(width-cidr)=key/2^(width-cidr))
    (downSide : downNode.bits/2^(width-1-cidr)%2=b)
    (internal : ∀ current node, (current,node) ∈ (target d).nodes → node.peer=none →
      internalListCheck newNames after current=.ok ()) :
    heap newNames (installedCoverRoot v4 downId b key cidr width pid (target d)) after=.ok () := by
  have below' : ∀ entry ∈ (target d).nodes, entry.1<(target d).nextNode := target_nodes_below related
  have unique := target_node_unique d
  have checks := (heap_checks names (target d) before).mp checked
  have tree := checks.1
  change Trie.heap (trieState (target d)) _=_ at tree
  have downBelow : downId<(target d).nextNode := below' _ down
  have downFresh : downId≠(target d).nextNode := Nat.ne_of_lt downBelow
  have rootMember : some downId ∈ [(target d).table.root4,(target d).table.root6] := by
    cases v4
    · have here : (target d).table.root6=some downId := by simpa using rootHere
      simp [here]
    · have here : (target d).table.root4=some downId := by simpa using rootHere
      simp [here]
  have absentFresh : ∀ entry ∈ (target d).nodes, some (target d).nextNode ∉ entry.2.bit.toList := by
    rintro ⟨id,node⟩ member child
    exact Nat.lt_irrefl _ (edges_below checked below' id node member _ child)
  have oldRootBelow : (target d).table.root4≠some (target d).nextNode ∧
      (target d).table.root6≠some (target d).nextNode := by
    constructor <;> intro equal
    · exact Nat.lt_irrefl _ (roots_below checked below' _ (by simp [equal]))
    · exact Nat.lt_irrefl _ (roots_below checked below' _ (by simp [equal]))
  have downNotHeld : ∀ entry ∈ (target d).nodes, some downId ∉ entry.2.bit.toList := by
    rintro ⟨id,node⟩ member child
    obtain ⟨index,atIndex⟩ := List.mem_iff_getElem?.mp child
    have edge : (some downId,index) ∈ (Trie.targetNode node).children.toList.zipIdx :=
      List.mk_mem_zipIdx_iff_getElem?.mpr atIndex
    obtain ⟨_,_,notRoot,_⟩ := Trie.heap_edge_facts tree id _
      (List.mem_map.mpr ⟨(id,node),member,rfl⟩) _ edge downId rfl
    exact notRoot rootMember
  have stepsOld (id : Nat) (e : NodeId×AipNode) (state : List Slot) :
      incomingStep id (reparent downId (.child (target d).nextNode b) e) state=incomingStep id e state :=
    incomingStep_same id (a:=reparent downId (.child (target d).nextNode b) e) (b:=e) rfl
      (reparent_bit _ _ _) state
  apply (heap_checks newNames _ after).mpr
  constructor
  · have nodes : ((installedCoverRoot v4 downId b key cidr width pid (target d)).nodes.map
        (fun (id,n) => (id,Trie.targetNode n)))=
        (trieState (target d)).nodes++
          [((target d).nextNode,Trie.targetNode (coverRootLeaf v4 downId b key cidr width pid))] := by
      simp only [trieState,installedCoverRoot,List.map_append,List.map_cons,List.map_nil,List.map_map]
      congr 1
      apply List.map_congr_left
      rintro ⟨current,node⟩ member
      by_cases q : current=downId
      · subst q
        simp [reparent,Trie.targetNode]
      · simp [reparent,Trie.targetNode,q]
    have counts : ((installedCoverRoot v4 downId b key cidr width pid (target d)).peers.map
        (fun (id,count,_) => (id,count)))=(target d).peers.map (fun (id,count,_) => (id,count)) := by
      simp only [installedCoverRoot,List.map_map]
      apply List.map_congr_left
      rintro ⟨a,b,c⟩ _
      rfl
    have trieEq : trieState (installedCoverRoot v4 downId b key cidr width pid (target d))=
        {trieState (target d) with nodes:=(trieState (target d)).nodes++
          [((target d).nextNode,Trie.targetNode (coverRootLeaf v4 downId b key cidr width pid))]} :=
      (congrArg (fun n => Trie.State.mk n _) nodes).trans (congrArg (Trie.State.mk _) counts)
    have rootsNew : ∀ r ∈ [(installedCoverRoot v4 downId b key cidr width pid (target d)).table.root4,
        (installedCoverRoot v4 downId b key cidr width pid (target d)).table.root6],
        r=some (target d).nextNode ∨
          (r ∈ [(target d).table.root4,(target d).table.root6] ∧ r≠some downId) := by
      intro r member
      cases v4
      · have cases : r=(target d).table.root4 ∨ r=some (target d).nextNode := by
          simpa [installedCoverRoot] using member
        rcases cases with rfl|rfl
        · exact .inr ⟨by simp,by simpa using otherRoot⟩
        · exact .inl rfl
      · have cases : r=some (target d).nextNode ∨ r=(target d).table.root6 := by
          simpa [installedCoverRoot] using member
        rcases cases with rfl|rfl
        · exact .inl rfl
        · exact .inr ⟨by simp,by simpa using otherRoot⟩
    change Trie.heap (trieState (installedCoverRoot v4 downId b key cidr width pid (target d))) _=_
    rw [trieEq]
    exact Trie.C1Cover.heap_root_covered (downNode:=Trie.targetNode downNode) tree
      (by simpa only [trieState,List.map_map,Function.comp_def] using unique)
      (fun entry member => by
        obtain ⟨old,present,equal⟩ := List.mem_map.mp member
        exact (congrArg Prod.fst equal) ▸ Nat.ne_of_lt (below' old present))
      (List.mem_map.mpr ⟨(downId,downNode),down,rfl⟩) rootMember rootsNew
      bit rfl downWidth downMeasure downPrefix downSide
  · intro id node member
    rcases List.mem_append.mp member with old | newLeaf
    · obtain ⟨⟨current,original⟩,present,equal⟩ := List.mem_map.mp old
      have currentBelow : current<(target d).nextNode := below' _ present
      have notFresh : current≠(target d).nextNode := Nat.ne_of_lt currentBelow
      have goal : structureCheck (installedCoverRoot v4 downId b key cidr width pid (target d)) current
          (reparent downId (.child (target d).nextNode b) (current,original)).2=.ok () ∧
          ownershipCheck newNames (installedCoverRoot v4 downId b key cidr width pid (target d)) after current
          (reparent downId (.child (target d).nextNode b) (current,original)).2=.ok () := by
        constructor
        · by_cases isDown : current=downId
          · subst current
            have others : (installedCoverRoot v4 downId b key cidr width pid (target d)).table.root4≠some downId ∧
                (installedCoverRoot v4 downId b key cidr width pid (target d)).table.root6≠some downId := by
              cases v4
              · exact ⟨by simpa [installedCoverRoot] using otherRoot,
                  by simp [installedCoverRoot,Ne.symm downFresh]⟩
              · exact ⟨by simp [installedCoverRoot,Ne.symm downFresh],
                  by simpa [installedCoverRoot] using otherRoot⟩
            have walk : forIn (installedCoverRoot v4 downId b key cidr width pid (target d)).nodes []
                (incomingStep downId)=.ok [Slot.child (target d).nextNode b] := by
              apply C1Split.walk_last
              · intro pair member current
                obtain ⟨entry,atEntry,rfl⟩ := List.mem_map.mp member
                rw [stepsOld _ entry]
                exact incomingStep_absent downId _ (downNotHeld entry atEntry) current
              · exact incomingStep_coverRootLeaf bit []
            exact structureCheck_single others.1 others.2 walk (by simp [reparent])
          · have same : reparent downId (.child (target d).nextNode b) (current,original)=
                (current,original) := by simp [reparent,isDown]
            rw [same]
            have oldCheck := (checks.2 current original present).1
            rw [structureCheck_walk] at oldCheck ⊢
            have rootsEq : forIn [((installedCoverRoot v4 downId b key cidr width pid (target d)).table.root4,
                  Slot.root4,32),
                ((installedCoverRoot v4 downId b key cidr width pid (target d)).table.root6,Slot.root6,128)] []
                (rootStep current original)=
                forIn [((target d).table.root4,Slot.root4,32),((target d).table.root6,Slot.root6,128)] []
                  (rootStep current original) := by
              cases v4
              · have here : (target d).table.root6=some downId := by simpa using rootHere
                simp [installedCoverRoot,rootStep,here,Ne.symm notFresh,Ne.symm isDown]
              · have here : (target d).table.root4=some downId := by simpa using rootHere
                simp [installedCoverRoot,rootStep,here,Ne.symm notFresh,Ne.symm isDown]
            have children (initial : List Slot) :
                forIn (installedCoverRoot v4 downId b key cidr width pid (target d)).nodes initial
                  (incomingStep current)=forIn (target d).nodes initial (incomingStep current) := by
              change forIn (((target d).nodes.map (reparent downId (.child (target d).nextNode b)))++
                [((target d).nextNode,coverRootLeaf v4 downId b key cidr width pid)]) initial
                (incomingStep current)=_
              rw [forIn_append_identity (fun pair member state => by
                obtain rfl := List.mem_singleton.mp member
                exact incomingStep_absent current _ (coverRootLeaf_absent bit isDown) state)]
              rw [List.forIn_map]
              apply forIn_congr_mem
              rintro ⟨other,otherNode⟩ _ state
              exact stepsOld current _ state
            rw [rootsEq,←oldCheck]
            congr 1
            funext incoming
            rw [children]
        · have peerSame := reparent_peer downId (.child (target d).nextNode b) (current,original)
          apply ownershipCheck_of
          · rw [peerSame]
            exact (owners_installed_other (target d) true key cidr pid current notFresh).trans
              (heap_ownership checked current original present).1
          · rw [peerSame]
            exact internal current original present
      cases equal
      exact goal
    · obtain equal := List.mem_singleton.mp newLeaf
      cases equal
      constructor
      · rw [structureCheck_walk]
        have walkI (initial : List Slot) :
            forIn (installedCoverRoot v4 downId b key cidr width pid (target d)).nodes initial
              (incomingStep (target d).nextNode)=.ok initial := by
          apply forIn_identity
          intro pair member state
          rcases List.mem_append.mp member with mapped | last
          · obtain ⟨entry,atEntry,rfl⟩ := List.mem_map.mp mapped
            rw [stepsOld _ entry]
            exact incomingStep_absent _ _ (absentFresh entry atEntry) state
          · obtain rfl := List.mem_singleton.mp last
            exact incomingStep_absent _ _ (coverRootLeaf_absent bit (Ne.symm downFresh)) state
        cases v4
        · have wide : width=128 := by simpa using family
          subst wide
          have rootsRun : forIn [((installedCoverRoot false downId b key cidr 128 pid (target d)).table.root4,
                Slot.root4,32),
              ((installedCoverRoot false downId b key cidr 128 pid (target d)).table.root6,Slot.root6,128)] []
              (rootStep (target d).nextNode (coverRootLeaf false downId b key cidr 128 pid))=
              .ok [Slot.root6] := by
            simp [installedCoverRoot,rootStep,oldRootBelow.1,newNode]
            rfl
          rw [rootsRun]
          dsimp only [Bind.bind,Except.bind]
          rw [walkI]
          rfl
        · have wide : width=32 := by simpa using family
          subst wide
          have rootsRun : forIn [((installedCoverRoot true downId b key cidr 32 pid (target d)).table.root4,
                Slot.root4,32),
              ((installedCoverRoot true downId b key cidr 32 pid (target d)).table.root6,Slot.root6,128)] []
              (rootStep (target d).nextNode (coverRootLeaf true downId b key cidr 32 pid))=
              .ok [Slot.root4] := by
            simp [installedCoverRoot,rootStep,oldRootBelow.2,newNode]
            rfl
          rw [rootsRun]
          dsimp only [Bind.bind,Except.bind]
          rw [walkI]
          rfl
      · apply ownershipCheck_of
        · exact owners_installed_new related true key cidr pid owner hasPeer
        · simp [newNode]

#print axioms heap_installedCoverRoot
end Binary.Pair.Allowedips.C1Cover
