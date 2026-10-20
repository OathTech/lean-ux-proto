import AllowedipsRootAttachment

namespace Binary.Pair.Allowedips

theorem ids_below_counter {names o} (valid : validate names o=.ok ()) :
    ∀ p ∈ names.trie.nodes, p.1<names.nextNode := by
  unfold validate at valid
  obtain ⟨_,_,valid⟩ := bind_ok valid
  obtain ⟨_,valid⟩ := check_ok _ _ _ _ valid
  obtain ⟨_,_,valid⟩ := bind_ok valid
  obtain ⟨_,ids,_⟩ := bind_ok valid
  exact forIn_ok (P:=fun p : Nat×Nat => p.1<names.nextNode)
    (fun p _ _ _ run => by
      rcases p with ⟨id,address⟩
      dsimp only at run ⊢
      by_cases below : id<names.nextNode
      · simp only [below,ite_true] at run
        exact ⟨(),(Except.ok.inj run).symm,below⟩
      · simp only [below,ite_false] at run
        cases run) ids

theorem allocated_node (names : Names) (address : Nat) :
    (names.nextNode,address) ∈ (names.allocated address).trie.nodes := by
  simp [Names.allocated]

theorem target_nodes_below {names o m d} (related : Corresponds names o m d) :
    ∀ pair ∈ (target d).nodes, pair.1<d.nextNode := by
  have full := reconstruct_fields related
  have counter := ids_below_counter full.valid
  rintro ⟨current,node⟩ member
  obtain ⟨⟨id,base⟩,named,read⟩ := full.nodes.right (current,node) member
  have equal := (decodeNode_fields read).1
  have less := counter (id,base) named
  dsimp only at equal less
  rw [equal] at less
  simpa only [←full.nextNode,target] using less

theorem allocated_ids {names : Names} (address : Nat)
    (unique : (names.trie.nodes.map Prod.fst).Nodup)
    (bounded : ∀ p ∈ names.trie.nodes, p.1<names.nextNode) :
    ((names.allocated address).trie.nodes.map Prod.fst).Nodup := by
  simp only [Names.allocated,List.map_append,List.map_cons,List.map_nil,List.nodup_append]
  refine ⟨unique,by simp,?_⟩
  intro a member b singleton equal
  obtain ⟨p,present,identity⟩ := List.mem_map.mp member
  have below := bounded p present
  have bEq : b=names.nextNode := by simpa using singleton
  exact (Nat.ne_of_lt below) (identity.trans (equal.trans bEq))

theorem Ring.peerList_fresh {names m head fuel first previous entries}
    (decoded : peerList names m head fuel first previous []=.ok entries)
    (bounded : ∀ p ∈ names.trie.nodes, p.1<names.nextNode) : names.nextNode ∉ entries := by
  obtain ⟨nodes,entryEq,_,shape,_,_,_⟩ := Ring.peerList_shape decoded
  intro member
  rw [entryEq] at member
  obtain ⟨⟨link,id⟩,present,identity⟩ := List.mem_map.mp member
  obtain ⟨p,q,fields⟩ := shape.member_fields present
  have below := bounded (id,link-AllowedipsMutationLayout.peer_list) fields.named
  exact (Nat.ne_of_lt below) identity

/-- Physical ownership freshness extends allocation geometry. This does not
require a decoded fresh node or assume any of its future linkage. -/
theorem Geometry.allocate {names o address} (g : Geometry names o)
    (extent : address+o.nodeSize≤2^64)
    (fresh : ∀ span ∈ allocations names o, disjointRanges address o.nodeSize span.1 span.2=true) :
    Geometry (names.allocated address) o := by
  let ns := names.trie.nodes.map (fun p => (p.2,o.nodeSize))
  let ps := names.trie.peers.map (fun p => (p.2,Layouts.peerSize))
  have old : allocations names o=ns++ps := rfl
  have allocated : allocations (names.allocated address) o=(ns++[(address,o.nodeSize)])++ps := by
    simp only [allocations,Names.allocated,List.map_append,List.map_cons,List.map_nil,ns,ps]
  refine ⟨?_,?_⟩
  · intro span member
    rw [allocated] at member
    rcases List.mem_append.mp member with node|peer
    · rcases List.mem_append.mp node with oldNode|newNode
      · exact g.bounded span (old ▸ List.mem_append_left ps oldNode)
      · have equal : span=(address,o.nodeSize) := by simpa using newNode
        simpa only [equal] using extent
    · exact g.bounded span (old ▸ List.mem_append_right ns peer)
  · have oldPair := g.apart
    rw [old,List.pairwise_append] at oldPair
    rw [allocated,List.pairwise_append,List.pairwise_append]
    refine ⟨⟨oldPair.1,by simp,?_⟩,oldPair.2.1,?_⟩
    · intro a member b singleton
      have equal : b=(address,o.nodeSize) := by simpa using singleton
      subst b
      simpa only [disjointRanges,Bool.or_comm] using fresh a (old ▸ List.mem_append_left ps member)
    · intro a member b peer
      rcases List.mem_append.mp member with oldNode|newNode
      · exact oldPair.2.2 a oldNode b peer
      · have equal : a=(address,o.nodeSize) := by simpa using newNode
        subst a
        exact fresh b (old ▸ List.mem_append_right ns peer)

#print axioms Geometry.allocate
#print axioms ids_below_counter
end Binary.Pair.Allowedips
