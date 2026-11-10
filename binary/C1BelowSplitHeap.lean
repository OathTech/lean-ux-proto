import C1BelowSplitSource
import C1BelowSplitTrieHeap

/- Origin: trial source binary-trials/t5/T5Heap.lean on branch task/binary-trials (unreviewed), ported for C1 work
package 3 with module and namespace renames only unless a comment marked "C1 port" says otherwise. -/
/-! Trial T5, stage 2: the structural assertion `heap` is restored by the
intermediate insertion (non-NULL parent). -/
namespace Binary.Pair.Allowedips.C1Split
open Leanux Leanux.WG Root

abbrev intermediateLeaf (b2 key cidr width pid internalId : Nat) : AipNode :=
  {newNode key cidr width (some pid) with parent:=.child internalId b2}

abbrev intermediateInternal (downId b1 b2 parentId direction key common width leafId : Nat) : AipNode :=
  {newNode key common width none with
    bit:=((newNode key common width none).bit.set! b1 (some downId)).set! b2 (some leafId),
    parent:=.child parentId direction}

/-- The expected state with the old-record update written as t2's `coverUpdate`
(the two agree on every old identity), so that t2's walk lemmas apply. -/
def intermediateForm (downId b1 b2 parentId direction key cidr common width pid : Nat) (s : State) : State :=
  { s with
    nodes := s.nodes.map (coverUpdate downId b1 parentId direction (s.nextNode+1))++
      [(s.nextNode,intermediateLeaf b2 key cidr width pid (s.nextNode+1))]++
      [(s.nextNode+1,intermediateInternal downId b1 b2 parentId direction key common width s.nextNode)]
    peers := s.peers.map (appendOwner s.nextNode pid)
    nextNode := s.nextNode+1+1 }

theorem connectUpdate_cover {downId b1 parentId direction internalId : Nat} {entry : NodeId×AipNode}
    (old : entry.1≠internalId) :
    connectUpdate internalId parentId direction (connectUpdate downId internalId b1 entry)=
      coverUpdate downId b1 parentId direction internalId entry := by
  rcases entry with ⟨current,node⟩
  have old : current≠internalId := old
  by_cases p : current=parentId
  · subst p
    by_cases q : current=downId
    · subst q
      simp only [connectUpdate,coverUpdate,reparent,installChild,old,↓reduceIte]
    · simp only [connectUpdate,coverUpdate,reparent,installChild,old,q,↓reduceIte]
  · by_cases q : current=downId
    · subst q
      simp only [connectUpdate,coverUpdate,reparent,installChild,old,p,↓reduceIte]
    · simp only [connectUpdate,coverUpdate,reparent,installChild,old,p,q,↓reduceIte]

theorem installedIntermediate_form {downId b1 b2 parentId direction key cidr common width pid : Nat}
    {s : State} (below : ∀ entry ∈ s.nodes, entry.1<s.nextNode) :
    installedIntermediate downId b1 b2 parentId direction key cidr common width pid s=
      intermediateForm downId b1 b2 parentId direction key cidr common width pid s := by
  have nodes : s.nodes.map (fun e =>
      connectUpdate (s.nextNode+1) parentId direction (connectUpdate downId (s.nextNode+1) b1 e))=
      s.nodes.map (coverUpdate downId b1 parentId direction (s.nextNode+1)) := by
    apply List.map_congr_left
    intro entry member
    exact connectUpdate_cover (Nat.ne_of_lt (Nat.lt_succ_of_lt (below entry member)))
  simp only [installedIntermediate,intermediateForm,nodes]

theorem coverUpdate_peer' (downId b parentId direction fresh : Nat) (entry : NodeId×AipNode) :
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

theorem trieState_intermediateForm (s : State)
    (downId b1 b2 parentId direction key cidr common width pid : Nat) :
    trieState (intermediateForm downId b1 b2 parentId direction key cidr common width pid s)=
      {trieState s with nodes:=(trieState s).nodes.map (Trie.changeChild parentId direction (s.nextNode+1))++
        [(s.nextNode,Trie.targetNode (intermediateLeaf b2 key cidr width pid (s.nextNode+1)))]++
        [(s.nextNode+1,{Trie.targetNode {newNode key common width none with
            bit:=(newNode key common width none).bit.set! b1 (some downId)} with
          children:=(Trie.targetNode {newNode key common width none with
            bit:=(newNode key common width none).bit.set! b1 (some downId)}).children.set! b2
              (some s.nextNode)})]} := by
  have nodes : ((intermediateForm downId b1 b2 parentId direction key cidr common width pid s).nodes.map
      (fun (id,n) => (id,Trie.targetNode n)))=
      (trieState s).nodes.map (Trie.changeChild parentId direction (s.nextNode+1))++
        [(s.nextNode,Trie.targetNode (intermediateLeaf b2 key cidr width pid (s.nextNode+1)))]++
        [(s.nextNode+1,{Trie.targetNode {newNode key common width none with
            bit:=(newNode key common width none).bit.set! b1 (some downId)} with
          children:=(Trie.targetNode {newNode key common width none with
            bit:=(newNode key common width none).bit.set! b1 (some downId)}).children.set! b2
              (some s.nextNode)})] := by
    simp only [trieState,intermediateForm,List.map_append,List.map_cons,List.map_nil,List.map_map]
    congr 2
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
  have counts : ((intermediateForm downId b1 b2 parentId direction key cidr common width pid s).peers.map
      (fun (id,count,_) => (id,count)))=s.peers.map (fun (id,count,_) => (id,count)) := by
    simp only [intermediateForm,List.map_map]
    apply List.map_congr_left
    rintro ⟨a,b,c⟩ _
    rfl
  exact (congrArg (fun n => Trie.State.mk n _) nodes).trans (congrArg (Trie.State.mk _) counts)

theorem incomingStep_newLeaf (id b2 key cidr width pid internalId leafId : Nat) (before : List Slot) :
    incomingStep id (leafId,intermediateLeaf b2 key cidr width pid internalId) before=
      .ok (.yield before) :=
  incomingStep_absent id _ (by simp [newNode]) before

theorem internal_absent {id downId b1 b2 parentId direction key common width leafId : Nat}
    (bit1 : b1<2) (bit2 : b2<2) (notDown : id≠downId) (notLeaf : id≠leafId) :
    some id ∉ (intermediateInternal downId b1 b2 parentId direction key common width leafId).bit.toList := by
  have which1 : b1=0 ∨ b1=1 := by omega
  have which2 : b2=0 ∨ b2=1 := by omega
  rcases which1 with rfl|rfl <;> rcases which2 with rfl|rfl <;> simp [newNode,notDown,notLeaf]

theorem incomingStep_internal_down {downId b1 b2 parentId direction key common width leafId internalId : Nat}
    (bit1 : b1<2) (bit2 : b2<2) (sides : b1≠b2) (different : downId≠leafId) (before : List Slot) :
    incomingStep downId
      (internalId,intermediateInternal downId b1 b2 parentId direction key common width leafId) before=
      .ok (.yield (.child internalId b1::before)) := by
  have which1 : b1=0 ∨ b1=1 := by omega
  have which2 : b2=0 ∨ b2=1 := by omega
  rcases which1 with rfl|rfl <;> rcases which2 with rfl|rfl
  · exact absurd rfl sides
  · simp [incomingStep,newNode,Ne.symm different]
    rfl
  · simp [incomingStep,newNode,Ne.symm different]
    rfl
  · exact absurd rfl sides

theorem incomingStep_internal_leaf {downId b1 b2 parentId direction key common width leafId internalId : Nat}
    (bit1 : b1<2) (bit2 : b2<2) (sides : b1≠b2) (different : downId≠leafId) (before : List Slot) :
    incomingStep leafId
      (internalId,intermediateInternal downId b1 b2 parentId direction key common width leafId) before=
      .ok (.yield (.child internalId b2::before)) := by
  have which1 : b1=0 ∨ b1=1 := by omega
  have which2 : b2=0 ∨ b2=1 := by omega
  rcases which1 with rfl|rfl <;> rcases which2 with rfl|rfl
  · exact absurd rfl sides
  · simp [incomingStep,newNode,different]
    rfl
  · simp [incomingStep,newNode,different]
    rfl
  · exact absurd rfl sides

/-- A walk whose only contribution is the last entry. -/
theorem walk_last {front : List (NodeId×AipNode)} {id : Nat} {last : NodeId×AipNode} {slot : Slot}
    (steps : ∀ pair ∈ front, ∀ current, incomingStep id pair current=.ok (.yield current))
    (final : incomingStep id last []=.ok (.yield [slot])) :
    forIn (front++[last]) [] (incomingStep id)=.ok [slot] := by
  rw [forIn_append_yield (fun pair member before after run =>
    ⟨before,(Except.ok.inj ((steps pair member before).symm.trans run)).symm⟩) (forIn_identity steps [])]
  rw [List.forIn_cons,final]
  rfl

/-- All parts of the executable allowed-IPs heap assertion are restored by the
intermediate insertion with a non-NULL parent. -/
theorem heap_installedIntermediate {names newNames o before after d}
    {downId b1 b2 parentId direction key cidr common width pid : Nat}
    {parentNode downNode : AipNode} (owner : Peer)
    (related : Corresponds names o before d) (checked : heap names (target d) before=.ok ())
    (hasPeer : d.peers.get? pid=some owner)
    (parent : (parentId,parentNode) ∈ (target d).nodes) (down : (downId,downNode) ∈ (target d).nodes)
    (bit : direction<2) (bit1 : b1<2) (bit2 : b2<2)
    -- `down = parent->bit[choose(parent,key)]`, found non-NULL.
    (occupied : parentNode.bit[direction]?=some (some downId))
    -- the walk matched `parent`; `common` exceeds its prefix because `down` is on `key`'s side.
    (sameWidth : width=parentNode.bitlen) (measure : parentNode.cidr<common)
    (prefixEq : key/2^(parentNode.bitlen-parentNode.cidr)=parentNode.bits/2^(parentNode.bitlen-parentNode.cidr))
    (side : key/2^(parentNode.bitlen-1-parentNode.cidr)%2=direction)
    -- `common = common_bits(down,key,bits) < min(cidr, down->cidr)`: the non-covering branch.
    (downMeasure : common<downNode.cidr) (leafMeasure : common<cidr)
    (downPrefix : downNode.bits/2^(width-common)=key/2^(width-common))
    -- the two `choose(node, ·)` results, and that they differ (first differing bit).
    (downSide : downNode.bits/2^(width-1-common)%2=b1)
    (leafSide : key/2^(width-1-common)%2=b2) (sides : b1≠b2)
    (internal : ∀ current node, (current,node) ∈ (target d).nodes → node.peer=none →
      internalListCheck newNames after current=.ok ())
    (internalNew : internalListCheck newNames after ((target d).nextNode+1)=.ok ()) :
    heap newNames (installedIntermediate downId b1 b2 parentId direction key cidr common width pid (target d))
      after=.ok () := by
  have below := target_nodes_below related
  have below' : ∀ entry ∈ (target d).nodes, entry.1<(target d).nextNode := below
  rw [installedIntermediate_form below']
  have unique := target_node_unique d
  have checks := (heap_checks names (target d) before).mp checked
  obtain ⟨base,_,read⟩ := (reconstruct_fields related).node parent
  obtain ⟨left,right,_,_,shape,_⟩ := (Trie.decodeNode_fields (decodeNode_fields read).2).children
  change parentNode.bit=#[left,right] at shape
  have downBelow : downId<(target d).nextNode := below' _ down
  have parentBelow : parentId<(target d).nextNode := below' _ parent
  have downLeaf : downId≠(target d).nextNode := Nat.ne_of_lt downBelow
  have internalDown : (target d).nextNode+1≠downId := Ne.symm (Nat.ne_of_lt (Nat.lt_succ_of_lt downBelow))
  have internalLeaf : (target d).nextNode+1≠(target d).nextNode := Nat.succ_ne_self _
  have tree := checks.1
  change Trie.heap (trieState (target d)) _=_ at tree
  have trieParent : (parentId,Trie.targetNode parentNode) ∈ (trieState (target d)).nodes :=
    List.mem_map.mpr ⟨(parentId,parentNode),parent,rfl⟩
  have trieShape : (Trie.targetNode parentNode).children=#[left,right] := shape
  have trieOccupied : (Trie.targetNode parentNode).children[direction]?=some (some downId) := occupied
  -- no old record names a fresh identity as a child
  have absentFresh (x : Nat) (fresh : (target d).nextNode≤x) :
      ∀ entry ∈ (target d).nodes, some x ∉ entry.2.bit.toList := by
    rintro ⟨id,node⟩ member child
    have bound := edges_below checked below' id node member x child
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le bound fresh)
  -- after the parent's slot is redirected, no old record holds `x`, unless `x` is the new occupant
  have absentAfter (x : Nat) (notInternal : x≠(target d).nextNode+1)
      (elsewhere : ∀ entry ∈ (target d).nodes, entry≠(parentId,parentNode) → some x ∉ entry.2.bit.toList)
      (rightNe : direction=0 → right≠some x) (leftNe : direction=1 → left≠some x) :
      ∀ entry ∈ (target d).nodes,
        some x ∉ (installChild parentId direction ((target d).nextNode+1) entry).2.bit.toList := by
    rintro ⟨current,original⟩ present
    by_cases same : current=parentId
    · subst current
      have parentEq : original=parentNode := congrArg Prod.snd
        (Option.some.inj ((Trie.find_node_key unique present).symm.trans (Trie.find_node_key unique parent)))
      subst original
      have which : direction=0 ∨ direction=1 := by omega
      rcases which with rfl|rfl
      · have otherNe := rightNe rfl
        simp [installChild,shape,notInternal,Ne.symm otherNe]
      · have otherNe := leftNe rfl
        simp [installChild,shape,notInternal,Ne.symm otherNe]
    · simp only [installChild,ite_eq_right same]
      exact elsewhere (current,original) present (fun equal => same (congrArg Prod.fst equal))
  apply (heap_checks newNames _ after).mpr
  constructor
  · change Trie.heap (trieState (intermediateForm downId b1 b2 parentId direction key cidr common width pid
      (target d))) _=_
    rw [trieState_intermediateForm]
    exact Trie.C1Split.heap_intermediate (downNode:=Trie.targetNode downNode) tree
      (by simpa only [trieState,List.map_map,Function.comp_def] using unique)
      (fun entry member => by
        obtain ⟨old,present,equal⟩ := List.mem_map.mp member
        exact (congrArg Prod.fst equal) ▸ Nat.ne_of_lt (below old present))
      (fun entry member => by
        obtain ⟨old,present,equal⟩ := List.mem_map.mp member
        exact (congrArg Prod.fst equal) ▸ Nat.ne_of_lt (Nat.lt_succ_of_lt (below old present)))
      (Ne.symm internalLeaf) trieParent
      (List.mem_map.mpr ⟨(downId,downNode),down,rfl⟩) trieShape bit trieOccupied bit1 bit2 sides rfl rfl
      sameWidth measure prefixEq side downMeasure downPrefix downSide rfl leafMeasure rfl leafSide
  · intro id node member
    rcases List.mem_append.mp member with front | newInternal
    · rcases List.mem_append.mp front with old | newLeaf
      · -- an old record
        obtain ⟨⟨current,original⟩,present,equal⟩ := List.mem_map.mp old
        have currentBelow : current<(target d).nextNode := below' _ present
        have notLeaf : current≠(target d).nextNode := Nat.ne_of_lt currentBelow
        have notInternal : current≠(target d).nextNode+1 := Nat.ne_of_lt (Nat.lt_succ_of_lt currentBelow)
        have goal : structureCheck (intermediateForm downId b1 b2 parentId direction key cidr common width pid
            (target d)) current
            (coverUpdate downId b1 parentId direction ((target d).nextNode+1) (current,original)).2=.ok () ∧
            ownershipCheck newNames (intermediateForm downId b1 b2 parentId direction key cidr common width pid
              (target d)) after current
              (coverUpdate downId b1 parentId direction ((target d).nextNode+1) (current,original)).2=.ok () := by
          constructor
          · by_cases isDown : current=downId
            · subst current
              have downEq : original=downNode := congrArg Prod.snd
                (Option.some.inj ((Trie.find_node_key unique present).symm.trans (Trie.find_node_key unique down)))
              subst original
              have downEdge : (some downId,direction) ∈ (Trie.targetNode parentNode).children.toList.zipIdx := by
                apply List.mk_mem_zipIdx_iff_getElem?.mpr
                simpa using trieOccupied
              obtain ⟨_,_,notRoot,_⟩ := Trie.heap_edge_facts tree parentId _ trieParent _ downEdge downId rfl
              have other4 : (target d).table.root4≠some downId := fun equal => notRoot (by simp [equal])
              have other6 : (target d).table.root6≠some downId := fun equal => notRoot (by simp [equal])
              obtain ⟨elsewhere,rightNe,leftNe⟩ :=
                Trie.C1Split.heap_occupant_unique tree trieParent trieShape bit trieOccupied
              have absentAll := absentAfter downId (Ne.symm internalDown)
                (fun entry present different => elsewhere (entry.1,Trie.targetNode entry.2)
                  (List.mem_map.mpr ⟨entry,present,rfl⟩)
                  (fun equal => different (by
                    rcases entry with ⟨a,b⟩
                    have first : a=parentId := congrArg Prod.fst equal
                    subst first
                    exact congrArg (Prod.mk a) (congrArg Prod.snd
                      (Option.some.inj ((Trie.find_node_key unique present).symm.trans
                        (Trie.find_node_key unique parent)))))))
                rightNe leftNe
              have walk : forIn (intermediateForm downId b1 b2 parentId direction key cidr common width pid
                  (target d)).nodes [] (incomingStep downId)=.ok [Slot.child ((target d).nextNode+1) b1] := by
                apply walk_last
                · intro pair member current
                  rcases List.mem_append.mp member with mapped | leaf
                  · obtain ⟨entry,atEntry,rfl⟩ := List.mem_map.mp mapped
                    rw [incomingStep_cover]
                    exact incomingStep_absent downId _ (absentAll entry atEntry) current
                  · obtain rfl := List.mem_singleton.mp leaf
                    exact incomingStep_newLeaf _ _ _ _ _ _ _ _ current
                · exact incomingStep_internal_down bit1 bit2 sides downLeaf []
              have parentEq : (coverUpdate downId b1 parentId direction ((target d).nextNode+1)
                  (downId,downNode)).2.parent=.child ((target d).nextNode+1) b1 := by
                by_cases same : downId=parentId
                · subst same
                  simp [coverUpdate,reparent,installChild]
                · simp [coverUpdate,reparent,installChild,same]
              exact structureCheck_single other4 other6 walk parentEq
            · -- a bystander or the parent: the walk is the old walk
              have metadata (state : State) : structureCheck state current
                  (coverUpdate downId b1 parentId direction ((target d).nextNode+1) (current,original)).2=
                  structureCheck state current original := by
                by_cases same : current=parentId
                · simp only [coverUpdate,reparent,installChild,ite_eq_right isDown,ite_eq_left same]; rfl
                · simp only [coverUpdate,reparent,installChild,ite_eq_right isDown,ite_eq_right same]
              rw [metadata,structureCheck_walk]
              have children (initial : List Slot) :
                  forIn (intermediateForm downId b1 b2 parentId direction key cidr common width pid
                    (target d)).nodes initial (incomingStep current)=
                    forIn (target d).nodes initial (incomingStep current) := by
                change forIn (((target d).nodes.map
                  (coverUpdate downId b1 parentId direction ((target d).nextNode+1)))++
                  [((target d).nextNode,intermediateLeaf b2 key cidr width pid ((target d).nextNode+1))]++
                  [((target d).nextNode+1,intermediateInternal downId b1 b2 parentId direction key common width
                    (target d).nextNode)]) initial (incomingStep current)=_
                rw [forIn_append_identity (fun pair member state => by
                  obtain rfl := List.mem_singleton.mp member
                  exact incomingStep_absent current _ (internal_absent bit1 bit2 isDown notLeaf) state)]
                rw [forIn_append_identity (fun pair member state => by
                  obtain rfl := List.mem_singleton.mp member
                  exact incomingStep_newLeaf _ _ _ _ _ _ _ _ state)]
                rw [List.forIn_map]
                apply forIn_congr_mem
                rintro ⟨other,otherNode⟩ otherPresent state
                change incomingStep current (coverUpdate downId b1 parentId direction ((target d).nextNode+1)
                  (other,otherNode)) state=incomingStep current (other,otherNode) state
                rw [incomingStep_cover]
                by_cases same : other=parentId
                · subst other
                  have parentEq : otherNode=parentNode := congrArg Prod.snd
                    (Option.some.inj ((Trie.find_node_key unique otherPresent).symm.trans
                      (Trie.find_node_key unique parent)))
                  subst otherNode
                  exact incomingStep_replace_old shape bit occupied notInternal isDown state
                · simp only [installChild,ite_eq_right same]
              simp only [show (intermediateForm downId b1 b2 parentId direction key cidr common width pid
                (target d)).table=(target d).table from rfl]
              have oldCheck := (checks.2 current original present).1
              rw [structureCheck_walk] at oldCheck
              rw [←oldCheck]
              congr 1
              funext incoming
              rw [children]
          · have peerSame := coverUpdate_peer' downId b1 parentId direction ((target d).nextNode+1)
              (current,original)
            apply ownershipCheck_of
            · rw [peerSame]
              exact (owners_installed_other (target d) true key cidr pid current notLeaf).trans
                (heap_ownership checked current original present).1
            · rw [peerSame]
              exact internal current original present
        cases equal
        exact goal
      · -- the leaf
        obtain equal := List.mem_singleton.mp newLeaf
        cases equal
        constructor
        · have other4 : (target d).table.root4≠some (target d).nextNode := by
            intro equal
            have bound := roots_below checked below' (target d).nextNode (by simp [equal])
            exact Nat.lt_irrefl _ bound
          have other6 : (target d).table.root6≠some (target d).nextNode := by
            intro equal
            have bound := roots_below checked below' (target d).nextNode (by simp [equal])
            exact Nat.lt_irrefl _ bound
          have absentAll := absentAfter (target d).nextNode (Ne.symm internalLeaf)
            (fun entry present _ => absentFresh _ (Nat.le_refl _) entry present)
            (fun _ equal => absentFresh _ (Nat.le_refl _) _ parent (by simp [shape,equal]))
            (fun _ equal => absentFresh _ (Nat.le_refl _) _ parent (by simp [shape,equal]))
          have walk : forIn (intermediateForm downId b1 b2 parentId direction key cidr common width pid
              (target d)).nodes [] (incomingStep (target d).nextNode)=
              .ok [Slot.child ((target d).nextNode+1) b2] := by
            apply walk_last
            · intro pair member current
              rcases List.mem_append.mp member with mapped | leaf
              · obtain ⟨entry,atEntry,rfl⟩ := List.mem_map.mp mapped
                rw [incomingStep_cover]
                exact incomingStep_absent _ _ (absentAll entry atEntry) current
              · obtain rfl := List.mem_singleton.mp leaf
                exact incomingStep_newLeaf _ _ _ _ _ _ _ _ current
            · exact incomingStep_internal_leaf bit1 bit2 sides downLeaf []
          exact structureCheck_single other4 other6 walk rfl
        · apply ownershipCheck_of
          · exact owners_installed_new related true key cidr pid owner hasPeer
          · simp [newNode]
    · -- the internal node
      obtain equal := List.mem_singleton.mp newInternal
      cases equal
      constructor
      · have other4 : (target d).table.root4≠some ((target d).nextNode+1) := by
          intro equal
          have bound := roots_below checked below' ((target d).nextNode+1) (by simp [equal])
          exact Nat.lt_irrefl _ (Nat.lt_trans (Nat.lt_succ_self _) bound)
        have other6 : (target d).table.root6≠some ((target d).nextNode+1) := by
          intro equal
          have bound := roots_below checked below' ((target d).nextNode+1) (by simp [equal])
          exact Nat.lt_irrefl _ (Nat.lt_trans (Nat.lt_succ_self _) bound)
        have walk : forIn (intermediateForm downId b1 b2 parentId direction key cidr common width pid
            (target d)).nodes [] (incomingStep ((target d).nextNode+1))=
            .ok [Slot.child parentId direction] := by
          change forIn (((target d).nodes.map
            (coverUpdate downId b1 parentId direction ((target d).nextNode+1)))++
            [((target d).nextNode,intermediateLeaf b2 key cidr width pid ((target d).nextNode+1))]++
            [((target d).nextNode+1,intermediateInternal downId b1 b2 parentId direction key common width
              (target d).nextNode)]) [] (incomingStep ((target d).nextNode+1))=_
          rw [forIn_append_identity (fun pair member state => by
            obtain rfl := List.mem_singleton.mp member
            exact incomingStep_absent _ _ (internal_absent bit1 bit2 internalDown internalLeaf) state)]
          rw [forIn_append_identity (fun pair member state => by
            obtain rfl := List.mem_singleton.mp member
            exact incomingStep_newLeaf _ _ _ _ _ _ _ _ state)]
          exact incoming_cover_walk unique parent shape bit (absentFresh _ (Nat.le_succ _)) []
        exact structureCheck_single other4 other6 walk rfl
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

#print axioms heap_installedIntermediate
end Binary.Pair.Allowedips.C1Split
