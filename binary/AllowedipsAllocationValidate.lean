import AllowedipsValidateConstruct

namespace Binary.Pair.Allowedips

/-- Fresh owned storage extends the very same interpretation validation used
at runtime. Its node bytes need not yet be initialized or reconstructible. -/
theorem validate_allocate {names o m d address}
    (related : Corresponds names o m d)
    (positive : 0<address) (aligned : address%8=0)
    (extent : address+o.nodeSize<2^64)
    (fresh : ∀ span ∈ allocations names o, disjointRanges address o.nodeSize span.1 span.2=true)
    (tableApart : disjointRanges address o.nodeSize names.table AllowedipsMutationLayout.tableSize=true) :
    validate (names.allocated address) o=.ok () := by
  let n := names.allocated address
  have core := Trie.reconstruct_fields related.trie
  have layout : o.nodeSize=72 := core.layout.1
  have full := reconstruct_fields related
  have counter := ids_below_counter full.valid
  have g := (geometry related).allocate (Nat.le_of_lt extent) fresh
  have absent : ∀ pair ∈ names.trie.nodes, pair.2≠address := by
    intro pair member same
    have separated := fresh (pair.2,o.nodeSize) (node_allocation member)
    simp only [disjointRanges,Bool.or_eq_true,decide_eq_true_eq,same,layout] at separated
    omega
  have nodeAddresses : (n.trie.nodes.map Prod.snd).Nodup := by
    simp only [n,Names.allocated,List.map_append,List.map_cons,List.map_nil,List.nodup_append]
    refine ⟨(name_addresses related).1,by simp,?_⟩
    intro a member b singleton equal
    obtain ⟨pair,present,atAddress⟩ := List.mem_map.mp member
    have bEq : b=address := by simpa using singleton
    exact absent pair present (atAddress.trans (equal.trans bEq))
  have oldValid := full.valid
  unfold validate at oldValid
  obtain ⟨_,trieValid,oldValid⟩ := bind_ok oldValid
  obtain ⟨table,oldValid⟩ := check_ok _ _ _ _ oldValid
  obtain ⟨_,alignRun,oldValid⟩ := bind_ok oldValid
  obtain ⟨_,_,oldValid⟩ := bind_ok oldValid
  obtain ⟨_,tableRun,_⟩ := bind_ok oldValid
  have oldAligned : ∀ pair ∈ names.trie.nodes, pair.2%8=0 := by
    exact forIn_ok (P:=fun pair : Nat×Nat => pair.2%8=0)
      (fun pair _ _ _ run => by
        obtain ⟨checked,run⟩ := check_ok _ _ _ _ run
        exact ⟨(),(Except.ok.inj run).symm,by simpa using checked⟩) alignRun
  have oldTable : ∀ span ∈ allocations names o,
      disjointRanges span.1 span.2 names.table AllowedipsMutationLayout.tableSize=true := by
    exact forIn_ok (P:=fun span : Span => disjointRanges span.1 span.2 names.table AllowedipsMutationLayout.tableSize=true)
      (fun span _ _ _ run => by
        obtain ⟨checked,run⟩ := check_ok _ _ _ _ run
        exact ⟨(),(Except.ok.inj run).symm,checked⟩) tableRun
  have extendedMember {span} (member : span ∈ allocations n o) :
      span ∈ allocations names o ∨ span=(address,o.nodeSize) := by
    simp only [allocations,n,Names.allocated,List.map_append,List.map_cons,List.map_nil,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with (oldNode|freshNode)|oldPeer
    · exact .inl (List.mem_append_left _ oldNode)
    · exact .inr freshNode
    · exact .inl (List.mem_append_right _ oldPeer)
  have allBounded : ∀ span ∈ allocations n o, 0<span.1 ∧ span.1+span.2<2^64 := by
    intro span member
    rcases extendedMember member with old|rfl
    · rcases List.mem_append.mp old with node|peer
      · obtain ⟨⟨id,base⟩,named,rfl⟩ := List.mem_map.mp node
        exact core.nodeRange id base named
      · obtain ⟨⟨id,base⟩,named,rfl⟩ := List.mem_map.mp peer
        exact core.peerRange id base named
    · exact ⟨positive,extent⟩
  have newTrie : Trie.validate n.trie o=.ok () := by
    unfold Trie.validate at trieValid
    obtain ⟨layoutCheck,_⟩ := check_ok _ _ _ _ trieValid
    apply trie_validate_construct layoutCheck _ allBounded g.apart
    intro pairs member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    · exact ⟨allocated_ids address core.nodeIds counter,nodeAddresses⟩
    · exact ⟨core.peerIds,(name_addresses related).2⟩
  have alignNew : forIn (m:=Decode) n.trie.nodes () (fun (pair : Nat×Nat) _ => do
      unless pair.2%8==0 do throw (⟨"node",pair.2,"unaligned allocation"⟩ : DecodeError)
      pure (.yield ()))=.ok () := by
    apply forIn_yield
    intro pair member
    have alignment : pair.2%8=0 := by
      rcases List.mem_append.mp member with old|new
      · exact oldAligned pair old
      · have same : pair=(names.nextNode,address) := by simpa using new
        simpa only [same] using aligned
    simp only [alignment,beq_self_eq_true,ite_true]
    rfl
  have counterNew : forIn (m:=Decode) n.trie.nodes () (fun (pair : Nat×Nat) _ => do
      unless pair.1<n.nextNode do throw (⟨"names.nextNode",pair.1,"identity beyond allocation counter"⟩ : DecodeError)
      pure (.yield ()))=.ok () := by
    apply forIn_yield
    intro pair member
    have small : pair.1<n.nextNode := by
      change pair.1<names.nextNode+1
      rcases List.mem_append.mp member with old|new
      · exact Nat.lt_trans (counter pair old) (Nat.lt_succ_self _)
      · have same : pair=(names.nextNode,address) := by simpa using new
        simp only [same]; omega
    simp only [small,ite_true]
    rfl
  have tableNew : forIn (m:=Decode) (allocations n o) () (fun (span : Span) _ => do
      unless disjointRanges span.1 span.2 n.table AllowedipsMutationLayout.tableSize do
        throw (⟨"table",span.1,"allocation overlaps table"⟩ : DecodeError)
      pure (.yield ()))=.ok () := by
    apply forIn_yield
    intro span member
    have separated : disjointRanges span.1 span.2 n.table AllowedipsMutationLayout.tableSize=true := by
      rcases extendedMember member with old|rfl
      · exact oldTable span old
      · exact tableApart
    simp only [separated,ite_true]
    rfl
  change validate n o=.ok ()
  unfold validate
  rw [newTrie]
  change (do
    unless 0<n.table && n.table%8==0 && n.table+AllowedipsMutationLayout.tableSize<2^64 do
      throw (⟨"table",n.table,"NULL, unaligned or wrapping table"⟩ : DecodeError)
    let _ ← forIn (m:=Decode) n.trie.nodes () _
    let _ ← forIn (m:=Decode) n.trie.nodes () _
    let _ ← forIn (m:=Decode) (allocations n o) () _
    pure ())=.ok ()
  apply check_of _ _ _ _ table
  rw [alignNew,counterNew,tableNew]
  rfl

#print axioms validate_allocate
end Binary.Pair.Allowedips
