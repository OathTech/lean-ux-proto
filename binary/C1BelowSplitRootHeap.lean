import C1BelowSplitPathRoot

/- Origin: trial source binary-trials/t5/T5RootHeap.lean on branch task/binary-trials (unreviewed), ported for C1 work
package 3 with module and namespace renames only unless a comment marked "C1 port" says otherwise. -/
/-! Trial T5, stage 2, NULL-parent subcase: `heap` after the internal node replaces
`down` as the root of its family. -/
namespace Binary.Pair.Trie.C1Split
open Leanux Leanux.WG

/-- A fresh internal node becomes a root in place of `down`, with `down` and a fresh
leaf as its two children. -/
theorem heap_root_spliced {s : State} {roots roots' : List (Option NodeId)}
    {leafId internalId downId b1 b2 : Nat} {downNode leaf internal : Node}
    (checked : heap s roots=.ok ()) (unique : (s.nodes.map Prod.fst).Nodup)
    (absentLeaf : ∀ entry ∈ s.nodes, entry.1≠leafId)
    (absentInternal : ∀ entry ∈ s.nodes, entry.1≠internalId)
    (distinct : leafId≠internalId)
    (down : (downId,downNode) ∈ s.nodes) (downRoot : some downId ∈ roots)
    (rootsNew : ∀ r ∈ roots', r=some internalId ∨ (r ∈ roots ∧ r≠some downId))
    (bit1 : b1<2) (bit2 : b2<2) (sides : b1≠b2)
    (internalChildren : internal.children=
      ((#[none,none] : Array (Option NodeId)).set! b1 (some downId)).set! b2 (some leafId))
    (leafChildren : leaf.children=#[none,none])
    (downWidth : downNode.width=internal.width) (downMeasure : internal.cidr<downNode.cidr)
    (downPrefix : downNode.key/2^(internal.width-internal.cidr)=internal.key/2^(internal.width-internal.cidr))
    (downSide : downNode.key/2^(internal.width-1-internal.cidr)%2=b1)
    (leafWidth : leaf.width=internal.width) (leafMeasure : internal.cidr<leaf.cidr)
    (leafPrefix : leaf.key/2^(internal.width-internal.cidr)=internal.key/2^(internal.width-internal.cidr))
    (leafSide : leaf.key/2^(internal.width-1-internal.cidr)%2=b2) :
    heap {s with nodes:=s.nodes++[(leafId,leaf)]++[(internalId,internal)]} roots'=.ok () := by
  have downFound := find_node_key unique down
  have rootOld : ∀ next, some next ∈ roots' → next=internalId ∨ (some next ∈ roots ∧ next≠downId) := by
    intro next member
    rcases rootsNew _ member with equal | ⟨old,ne⟩
    · exact .inl (Option.some.inj equal)
    · exact .inr ⟨old,fun same => ne (congrArg some same)⟩
  have findOld {next : Nat} {child : Node} (found : s.nodes.find? (·.1==next)=some (next,child)) :
      (s.nodes++[(leafId,leaf)]++[(internalId,internal)]).find? (·.1==next)=some (next,child) := by
    simp only [List.find?_append,found,Option.some_or]
  have findLeaf : (s.nodes++[(leafId,leaf)]++[(internalId,internal)]).find? (·.1==leafId)=
      some (leafId,leaf) := by
    have missing : s.nodes.find? (·.1==leafId)=none :=
      List.find?_eq_none.mpr (fun entry member => by simpa using absentLeaf entry member)
    simp [List.find?_append,missing]
  have which1 : b1=0 ∨ b1=1 := by omega
  have which2 : b2=0 ∨ b2=1 := by omega
  apply heap_of_facts
  · intro id member
    rcases rootOld id member with rfl | ⟨old,_⟩
    · exact ⟨internal,List.mem_append_right _ (List.mem_singleton_self _)⟩
    · obtain ⟨node,present⟩ := heap_root checked old
      exact ⟨node,List.mem_append_left _ (List.mem_append_left _ present)⟩
  · intro id node member
    rcases List.mem_append.mp member with front | last
    · rcases List.mem_append.mp front with present | atLeaf
      · intro edge atEdge next equal
        obtain ⟨child,found,notRoot,rest⟩ := heap_edge_facts checked id node present edge atEdge next equal
        refine ⟨child,findOld found,?_,rest⟩
        intro member
        rcases rootOld next member with same | ⟨old,_⟩
        · exact absentInternal (next,child) (List.mem_of_find?_eq_some found) same
        · exact notRoot old
      · obtain equal := List.mem_singleton.mp atLeaf
        cases equal
        intro edge atEdge next equal
        rw [leafChildren] at atEdge
        have cases : edge=(none,0) ∨ edge=(none,1) := by simpa using atEdge
        rcases cases with rfl|rfl <;> cases equal
    · obtain equal := List.mem_singleton.mp last
      cases equal
      have downEdge : EdgeFacts {s with nodes:=s.nodes++[(leafId,leaf)]++[(internalId,internal)]} roots'
          internal (some downId,b1) := by
        intro next equal
        cases Option.some.inj equal
        refine ⟨downNode,findOld downFound,?_,downWidth,downMeasure,downPrefix,downSide⟩
        intro member
        rcases rootOld downId member with same | ⟨_,ne⟩
        · exact absentInternal _ down same
        · exact ne rfl
      have leafEdge : EdgeFacts {s with nodes:=s.nodes++[(leafId,leaf)]++[(internalId,internal)]} roots'
          internal (some leafId,b2) := by
        intro next equal
        cases Option.some.inj equal
        refine ⟨leaf,findLeaf,?_,leafWidth,leafMeasure,leafPrefix,leafSide⟩
        intro member
        rcases rootOld leafId member with same | ⟨old,_⟩
        · exact distinct same
        · obtain ⟨node,present⟩ := heap_root checked old
          exact absentLeaf _ present rfl
      intro edge atEdge
      rw [internalChildren] at atEdge
      rcases which1 with rfl|rfl <;> rcases which2 with rfl|rfl
      · exact absurd rfl sides
      · have cases : edge=(some downId,0) ∨ edge=(some leafId,1) := by simpa using atEdge
        rcases cases with rfl|rfl
        · exact downEdge
        · exact leafEdge
      · have cases : edge=(some leafId,0) ∨ edge=(some downId,1) := by simpa using atEdge
        rcases cases with rfl|rfl
        · exact leafEdge
        · exact downEdge
      · exact absurd rfl sides
  · have oldNodup := heap_children_nodup checked
    have leafFresh := heap_child_fresh checked absentLeaf
    have downNotChild : downId ∉ s.nodes.flatMap nodeChildren := by
      intro member
      obtain ⟨⟨id,node⟩,atNode,atChildren⟩ := List.mem_flatMap.mp member
      obtain ⟨edge,atEdge,atChild⟩ := List.mem_flatMap.mp atChildren
      have equal : edge.1=some downId := by simpa [edgeChildren] using atChild
      obtain ⟨_,_,notRoot,_⟩ := heap_edge_facts checked id node atNode edge atEdge downId equal
      exact notRoot downRoot
    have leafList : nodeChildren (leafId,leaf)=[] := by simp [nodeChildren,leafChildren,edgeChildren]
    have downLeaf : downId≠leafId := fun same => absentLeaf _ down same
    have internalList : nodeChildren (internalId,internal)=[downId,leafId] ∨
        nodeChildren (internalId,internal)=[leafId,downId] := by
      rcases which1 with rfl|rfl <;> rcases which2 with rfl|rfl
      · exact absurd rfl sides
      · exact .inl (by simp [nodeChildren,internalChildren,edgeChildren])
      · exact .inr (by simp [nodeChildren,internalChildren,edgeChildren])
      · exact absurd rfl sides
    simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,leafList,List.append_nil]
    have apart : ∀ a ∈ s.nodes.flatMap nodeChildren, ∀ b ∈ nodeChildren (internalId,internal), a≠b := by
      intro a member b atNew equal
      have which : b=downId ∨ b=leafId := by
        rcases internalList with list|list <;> rw [list] at atNew <;> simpa [or_comm] using atNew
      rcases which with rfl|rfl
      · exact downNotChild (equal ▸ member)
      · exact leafFresh (equal ▸ member)
    have newNodup : (nodeChildren (internalId,internal)).Nodup := by
      rcases internalList with list|list <;> rw [list]
      · simp [downLeaf]
      · simp [Ne.symm downLeaf]
    exact List.nodup_append.mpr ⟨oldNodup,newNodup,apart⟩

#print axioms heap_root_spliced
end Binary.Pair.Trie.C1Split

namespace Binary.Pair.Allowedips.C1Split
open Leanux Leanux.WG Root

abbrev rootInternal (v4 : Bool) (downId b1 b2 key common width leafId : Nat) : AipNode :=
  {newNode key common width none with
    bit:=((newNode key common width none).bit.set! b1 (some downId)).set! b2 (some leafId),
    parent:=if v4 then Slot.root4 else Slot.root6}

theorem incomingStep_congr (id : Nat) {a b : NodeId×AipNode} (key : a.1=b.1) (bits : a.2.bit=b.2.bit)
    (before : List Slot) : incomingStep id a before=incomingStep id b before := by
  unfold incomingStep
  rw [key,bits]

theorem connectUpdate_bit_old {downId internalId b1 : Nat} {entry : NodeId×AipNode}
    (old : entry.1≠internalId) : (connectUpdate downId internalId b1 entry).2.bit=entry.2.bit := by
  rcases entry with ⟨current,node⟩
  have old : current≠internalId := old
  by_cases q : current=downId
  · simp only [connectUpdate,q,↓reduceIte]
  · simp only [connectUpdate,q,old,↓reduceIte]

theorem connectUpdate_peer_old {downId internalId b1 : Nat} {entry : NodeId×AipNode}
    (old : entry.1≠internalId) : (connectUpdate downId internalId b1 entry).2.peer=entry.2.peer := by
  rcases entry with ⟨current,node⟩
  have old : current≠internalId := old
  by_cases q : current=downId
  · simp only [connectUpdate,q,↓reduceIte]
  · simp only [connectUpdate,q,old,↓reduceIte]

/-- `heap` after the intermediate insertion at the root of a family. -/
theorem heap_installedIntermediateRoot {names newNames o before after d} (v4 : Bool)
    {downId b1 b2 key cidr common width pid : Nat} {downNode : AipNode} (owner : Peer)
    (related : Corresponds names o before d) (checked : heap names (target d) before=.ok ())
    (hasPeer : d.peers.get? pid=some owner)
    (down : (downId,downNode) ∈ (target d).nodes)
    (bit1 : b1<2) (bit2 : b2<2)
    -- `down = *trie`, the root of this family, and of this family only
    (rootHere : (if v4 then (target d).table.root4 else (target d).table.root6)=some downId)
    (otherRoot : (if v4 then (target d).table.root6 else (target d).table.root4)≠some downId)
    (family : width=if v4 then 32 else 128) (downWidth : downNode.bitlen=width)
    (downMeasure : common<downNode.cidr) (leafMeasure : common<cidr)
    (downPrefix : downNode.bits/2^(width-common)=key/2^(width-common))
    (downSide : downNode.bits/2^(width-1-common)%2=b1)
    (leafSide : key/2^(width-1-common)%2=b2) (sides : b1≠b2)
    (internal : ∀ current node, (current,node) ∈ (target d).nodes → node.peer=none →
      internalListCheck newNames after current=.ok ())
    (internalNew : internalListCheck newNames after ((target d).nextNode+1)=.ok ()) :
    heap newNames (installedIntermediateRoot v4 downId b1 b2 key cidr common width pid (target d))
      after=.ok () := by
  have below' : ∀ entry ∈ (target d).nodes, entry.1<(target d).nextNode := target_nodes_below related
  have unique := target_node_unique d
  have checks := (heap_checks names (target d) before).mp checked
  have tree := checks.1
  change Trie.heap (trieState (target d)) _=_ at tree
  have downBelow : downId<(target d).nextNode := below' _ down
  have downLeaf : downId≠(target d).nextNode := Nat.ne_of_lt downBelow
  have internalDown : (target d).nextNode+1≠downId := Ne.symm (Nat.ne_of_lt (Nat.lt_succ_of_lt downBelow))
  have internalLeaf : (target d).nextNode+1≠(target d).nextNode := Nat.succ_ne_self _
  have rootMember : some downId ∈ [(target d).table.root4,(target d).table.root6] := by
    cases v4
    · have here : (target d).table.root6=some downId := by simpa using rootHere
      simp [here]
    · have here : (target d).table.root4=some downId := by simpa using rootHere
      simp [here]
  have absentFresh (x : Nat) (fresh : (target d).nextNode≤x) :
      ∀ entry ∈ (target d).nodes, some x ∉ entry.2.bit.toList := by
    rintro ⟨id,node⟩ member child
    have bound := edges_below checked below' id node member x child
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le bound fresh)
  have oldRootBelow (x : Nat) (fresh : (target d).nextNode≤x) :
      (target d).table.root4≠some x ∧ (target d).table.root6≠some x := by
    constructor <;> intro equal
    · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (roots_below checked below' x (by simp [equal])) fresh)
    · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (roots_below checked below' x (by simp [equal])) fresh)
  have downNotHeld : ∀ entry ∈ (target d).nodes, some downId ∉ entry.2.bit.toList := by
    rintro ⟨id,node⟩ member child
    obtain ⟨index,atIndex⟩ := List.mem_iff_getElem?.mp child
    have edge : (some downId,index) ∈ (Trie.targetNode node).children.toList.zipIdx :=
      List.mk_mem_zipIdx_iff_getElem?.mpr atIndex
    obtain ⟨_,_,notRoot,_⟩ := Trie.heap_edge_facts tree id _
      (List.mem_map.mpr ⟨(id,node),member,rfl⟩) _ edge downId rfl
    exact notRoot rootMember
  have stepsOld (id : Nat) (e : NodeId×AipNode) (member : e ∈ (target d).nodes) (state : List Slot) :
      incomingStep id (connectUpdate downId ((target d).nextNode+1) b1 e) state=incomingStep id e state :=
    incomingStep_congr id (a:=connectUpdate downId ((target d).nextNode+1) b1 e) (b:=e) rfl
      (connectUpdate_bit_old (Nat.ne_of_lt (Nat.lt_succ_of_lt (below' e member)))) state
  have stepInternal (id : Nat) (state : List Slot) :
      incomingStep id ((target d).nextNode+1,
        rootInternal v4 downId b1 b2 key common width (target d).nextNode) state=
      incomingStep id ((target d).nextNode+1,
        intermediateInternal downId b1 b2 0 0 key common width (target d).nextNode) state :=
    incomingStep_congr id rfl rfl state
  apply (heap_checks newNames _ after).mpr
  constructor
  · have nodes : ((installedIntermediateRoot v4 downId b1 b2 key cidr common width pid (target d)).nodes.map
        (fun (id,n) => (id,Trie.targetNode n)))=
        (trieState (target d)).nodes++
          [((target d).nextNode,Trie.targetNode
            (intermediateLeaf b2 key cidr width pid ((target d).nextNode+1)))]++
          [((target d).nextNode+1,Trie.targetNode
            (rootInternal v4 downId b1 b2 key common width (target d).nextNode))] := by
      simp only [trieState,installedIntermediateRoot,List.map_append,List.map_cons,List.map_nil,List.map_map]
      congr 2
      apply List.map_congr_left
      rintro ⟨current,node⟩ member
      have old : current≠(target d).nextNode+1 := Nat.ne_of_lt (Nat.lt_succ_of_lt (below' _ member))
      by_cases q : current=downId
      · subst q
        simp [connectUpdate,Trie.targetNode]
      · simp [connectUpdate,Trie.targetNode,q,old]
    have counts : ((installedIntermediateRoot v4 downId b1 b2 key cidr common width pid (target d)).peers.map
        (fun (id,count,_) => (id,count)))=(target d).peers.map (fun (id,count,_) => (id,count)) := by
      simp only [installedIntermediateRoot,List.map_map]
      apply List.map_congr_left
      rintro ⟨a,b,c⟩ _
      rfl
    have trieEq : trieState (installedIntermediateRoot v4 downId b1 b2 key cidr common width pid (target d))=
        {trieState (target d) with nodes:=(trieState (target d)).nodes++
          [((target d).nextNode,Trie.targetNode
            (intermediateLeaf b2 key cidr width pid ((target d).nextNode+1)))]++
          [((target d).nextNode+1,Trie.targetNode
            (rootInternal v4 downId b1 b2 key common width (target d).nextNode))]} :=
      (congrArg (fun n => Trie.State.mk n _) nodes).trans (congrArg (Trie.State.mk _) counts)
    have rootsNew : ∀ r ∈ [(installedIntermediateRoot v4 downId b1 b2 key cidr common width pid
          (target d)).table.root4,
        (installedIntermediateRoot v4 downId b1 b2 key cidr common width pid (target d)).table.root6],
        r=some ((target d).nextNode+1) ∨
          (r ∈ [(target d).table.root4,(target d).table.root6] ∧ r≠some downId) := by
      intro r member
      cases v4
      · have cases : r=(target d).table.root4 ∨ r=some ((target d).nextNode+1) := by
          simpa [installedIntermediateRoot] using member
        rcases cases with rfl|rfl
        · exact .inr ⟨by simp,by simpa using otherRoot⟩
        · exact .inl rfl
      · have cases : r=some ((target d).nextNode+1) ∨ r=(target d).table.root6 := by
          simpa [installedIntermediateRoot] using member
        rcases cases with rfl|rfl
        · exact .inl rfl
        · exact .inr ⟨by simp,by simpa using otherRoot⟩
    change Trie.heap (trieState (installedIntermediateRoot v4 downId b1 b2 key cidr common width pid
      (target d))) _=_
    rw [trieEq]
    exact Trie.C1Split.heap_root_spliced (downNode:=Trie.targetNode downNode) tree
      (by simpa only [trieState,List.map_map,Function.comp_def] using unique)
      (fun entry member => by
        obtain ⟨old,present,equal⟩ := List.mem_map.mp member
        exact (congrArg Prod.fst equal) ▸ Nat.ne_of_lt (below' old present))
      (fun entry member => by
        obtain ⟨old,present,equal⟩ := List.mem_map.mp member
        exact (congrArg Prod.fst equal) ▸ Nat.ne_of_lt (Nat.lt_succ_of_lt (below' old present)))
      (Ne.symm internalLeaf) (List.mem_map.mpr ⟨(downId,downNode),down,rfl⟩) rootMember rootsNew
      bit1 bit2 sides rfl rfl downWidth downMeasure downPrefix downSide rfl leafMeasure rfl leafSide
  · intro id node member
    rcases List.mem_append.mp member with front | newInternal
    · rcases List.mem_append.mp front with old | newLeaf
      · obtain ⟨⟨current,original⟩,present,equal⟩ := List.mem_map.mp old
        have currentBelow : current<(target d).nextNode := below' _ present
        have notLeaf : current≠(target d).nextNode := Nat.ne_of_lt currentBelow
        have notInternal : current≠(target d).nextNode+1 := Nat.ne_of_lt (Nat.lt_succ_of_lt currentBelow)
        have goal : structureCheck (installedIntermediateRoot v4 downId b1 b2 key cidr common width pid
            (target d)) current
            (connectUpdate downId ((target d).nextNode+1) b1 (current,original)).2=.ok () ∧
            ownershipCheck newNames (installedIntermediateRoot v4 downId b1 b2 key cidr common width pid
              (target d)) after current
              (connectUpdate downId ((target d).nextNode+1) b1 (current,original)).2=.ok () := by
          constructor
          · by_cases isDown : current=downId
            · subst current
              have others : (installedIntermediateRoot v4 downId b1 b2 key cidr common width pid
                  (target d)).table.root4≠some downId ∧
                  (installedIntermediateRoot v4 downId b1 b2 key cidr common width pid
                  (target d)).table.root6≠some downId := by
                cases v4
                · exact ⟨by simpa [installedIntermediateRoot] using otherRoot,
                    by simp [installedIntermediateRoot,internalDown]⟩
                · exact ⟨by simp [installedIntermediateRoot,internalDown],
                    by simpa [installedIntermediateRoot] using otherRoot⟩
              have walk : forIn (installedIntermediateRoot v4 downId b1 b2 key cidr common width pid
                  (target d)).nodes [] (incomingStep downId)=.ok [Slot.child ((target d).nextNode+1) b1] := by
                apply walk_last
                · intro pair member current
                  rcases List.mem_append.mp member with mapped | leaf
                  · obtain ⟨entry,atEntry,rfl⟩ := List.mem_map.mp mapped
                    rw [stepsOld _ entry atEntry]
                    exact incomingStep_absent downId _ (downNotHeld entry atEntry) current
                  · obtain rfl := List.mem_singleton.mp leaf
                    exact incomingStep_newLeaf _ _ _ _ _ _ _ _ current
                · exact (stepInternal downId []).trans
                    (incomingStep_internal_down bit1 bit2 sides downLeaf [])
              exact structureCheck_single others.1 others.2 walk (by simp [connectUpdate])
            · have same : connectUpdate downId ((target d).nextNode+1) b1 (current,original)=
                  (current,original) := connectUpdate_other isDown notInternal
              rw [same]
              have oldCheck := (checks.2 current original present).1
              rw [structureCheck_walk] at oldCheck ⊢
              have rootsEq : forIn [((installedIntermediateRoot v4 downId b1 b2 key cidr common width pid
                    (target d)).table.root4,Slot.root4,32),
                  ((installedIntermediateRoot v4 downId b1 b2 key cidr common width pid
                    (target d)).table.root6,Slot.root6,128)] [] (rootStep current original)=
                  forIn [((target d).table.root4,Slot.root4,32),((target d).table.root6,Slot.root6,128)] []
                    (rootStep current original) := by
                cases v4
                · have here : (target d).table.root6=some downId := by simpa using rootHere
                  simp [installedIntermediateRoot,rootStep,here,Ne.symm notInternal,Ne.symm isDown]
                · have here : (target d).table.root4=some downId := by simpa using rootHere
                  simp [installedIntermediateRoot,rootStep,here,Ne.symm notInternal,Ne.symm isDown]
              have children (initial : List Slot) :
                  forIn (installedIntermediateRoot v4 downId b1 b2 key cidr common width pid
                    (target d)).nodes initial (incomingStep current)=
                    forIn (target d).nodes initial (incomingStep current) := by
                change forIn (((target d).nodes.map (connectUpdate downId ((target d).nextNode+1) b1))++
                  [((target d).nextNode,intermediateLeaf b2 key cidr width pid ((target d).nextNode+1))]++
                  [((target d).nextNode+1,rootInternal v4 downId b1 b2 key common width
                    (target d).nextNode)]) initial (incomingStep current)=_
                rw [forIn_append_identity (fun pair member state => by
                  obtain rfl := List.mem_singleton.mp member
                  exact (stepInternal current state).trans
                    (incomingStep_absent current _ (internal_absent bit1 bit2 isDown notLeaf) state))]
                rw [forIn_append_identity (fun pair member state => by
                  obtain rfl := List.mem_singleton.mp member
                  exact incomingStep_newLeaf _ _ _ _ _ _ _ _ state)]
                rw [List.forIn_map]
                apply forIn_congr_mem
                rintro ⟨other,otherNode⟩ otherPresent state
                exact stepsOld current _ otherPresent state
              rw [rootsEq,←oldCheck]
              congr 1
              funext incoming
              rw [children]
          · have peerSame := connectUpdate_peer_old (downId:=downId) (b1:=b1)
              (entry:=(current,original)) notInternal
            apply ownershipCheck_of
            · rw [peerSame]
              exact (owners_installed_other (target d) true key cidr pid current notLeaf).trans
                (heap_ownership checked current original present).1
            · rw [peerSame]
              exact internal current original present
        cases equal
        exact goal
      · obtain equal := List.mem_singleton.mp newLeaf
        cases equal
        constructor
        · have old := oldRootBelow (target d).nextNode (Nat.le_refl _)
          have others : (installedIntermediateRoot v4 downId b1 b2 key cidr common width pid
              (target d)).table.root4≠some (target d).nextNode ∧
              (installedIntermediateRoot v4 downId b1 b2 key cidr common width pid
              (target d)).table.root6≠some (target d).nextNode := by
            cases v4
            · exact ⟨by simpa [installedIntermediateRoot] using old.1,
                by simp [installedIntermediateRoot]⟩
            · exact ⟨by simp [installedIntermediateRoot],
                by simpa [installedIntermediateRoot] using old.2⟩
          have walk : forIn (installedIntermediateRoot v4 downId b1 b2 key cidr common width pid
              (target d)).nodes [] (incomingStep (target d).nextNode)=
              .ok [Slot.child ((target d).nextNode+1) b2] := by
            apply walk_last
            · intro pair member current
              rcases List.mem_append.mp member with mapped | leaf
              · obtain ⟨entry,atEntry,rfl⟩ := List.mem_map.mp mapped
                rw [stepsOld _ entry atEntry]
                exact incomingStep_absent _ _ (absentFresh _ (Nat.le_refl _) entry atEntry) current
              · obtain rfl := List.mem_singleton.mp leaf
                exact incomingStep_newLeaf _ _ _ _ _ _ _ _ current
            · exact (stepInternal (target d).nextNode []).trans
                (incomingStep_internal_leaf bit1 bit2 sides downLeaf [])
          exact structureCheck_single others.1 others.2 walk rfl
        · apply ownershipCheck_of
          · exact owners_installed_new related true key cidr pid owner hasPeer
          · simp [newNode]
    · obtain equal := List.mem_singleton.mp newInternal
      cases equal
      constructor
      · rw [structureCheck_walk]
        have walkI (initial : List Slot) :
            forIn (installedIntermediateRoot v4 downId b1 b2 key cidr common width pid
              (target d)).nodes initial (incomingStep ((target d).nextNode+1))=.ok initial := by
          apply forIn_identity
          intro pair member state
          rcases List.mem_append.mp member with front | last
          · rcases List.mem_append.mp front with mapped | leaf
            · obtain ⟨entry,atEntry,rfl⟩ := List.mem_map.mp mapped
              rw [stepsOld _ entry atEntry]
              exact incomingStep_absent _ _ (absentFresh _ (Nat.le_succ _) entry atEntry) state
            · obtain rfl := List.mem_singleton.mp leaf
              exact incomingStep_newLeaf _ _ _ _ _ _ _ _ state
          · obtain rfl := List.mem_singleton.mp last
            exact (stepInternal _ state).trans
              (incomingStep_absent _ _ (internal_absent bit1 bit2 internalDown internalLeaf) state)
        have old := oldRootBelow ((target d).nextNode+1) (Nat.le_succ _)
        cases v4
        · have wide : width=128 := by simpa using family
          subst wide
          have rootsRun : forIn [((installedIntermediateRoot false downId b1 b2 key cidr common 128 pid
                (target d)).table.root4,Slot.root4,32),
              ((installedIntermediateRoot false downId b1 b2 key cidr common 128 pid
                (target d)).table.root6,Slot.root6,128)] []
              (rootStep ((target d).nextNode+1)
                (rootInternal false downId b1 b2 key common 128 (target d).nextNode))=.ok [Slot.root6] := by
            simp [installedIntermediateRoot,rootStep,old.1,newNode]
            rfl
          rw [rootsRun]
          dsimp only [Bind.bind,Except.bind]
          rw [walkI]
          rfl
        · have wide : width=32 := by simpa using family
          subst wide
          have rootsRun : forIn [((installedIntermediateRoot true downId b1 b2 key cidr common 32 pid
                (target d)).table.root4,Slot.root4,32),
              ((installedIntermediateRoot true downId b1 b2 key cidr common 32 pid
                (target d)).table.root6,Slot.root6,128)] []
              (rootStep ((target d).nextNode+1)
                (rootInternal true downId b1 b2 key common 32 (target d).nextNode))=.ok [Slot.root4] := by
            simp [installedIntermediateRoot,rootStep,old.2,newNode]
            rfl
          rw [rootsRun]
          dsimp only [Bind.bind,Except.bind]
          rw [walkI]
          rfl
      · apply ownershipCheck_of
        · have none : owners (target d) ((target d).nextNode+1)=[] := by
            apply List.eq_nil_iff_forall_not_mem.mpr
            intro p present
            obtain ⟨⟨current,count,entries⟩,member,found⟩ := List.mem_flatMap.mp present
            obtain ⟨x,atList,value⟩ := List.mem_filterMap.mp found
            by_cases same : x=(target d).nextNode+1
            · obtain ⟨node,isNode⟩ := (reconstruct_fields related).list_node member (same ▸ atList)
              have bound := below' _ isNode
              exact Nat.lt_irrefl _ (Nat.lt_trans (Nat.lt_succ_self _) bound)
            · simp [same] at value
          exact (owners_installed_other (target d) true key cidr pid ((target d).nextNode+1)
            internalLeaf).trans none
        · intro _
          exact internalNew

#print axioms heap_installedIntermediateRoot
end Binary.Pair.Allowedips.C1Split
