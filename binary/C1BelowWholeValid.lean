import AllowedipsAllocationValidate
import C1BelowSplitGeneric

/-! Result C1, work package 3, the split path: extending a valid
interpretation by a second fresh object. The landed `validate_allocate`
takes a full relation for the names being extended; after the first
allocation there is none (the pending node has no parent word yet), so the
same construction is repeated here from the validity of the names alone.
Origin: `AllowedipsAllocationValidate.validate_allocate`, with the facts it
took from the relation taken from `validate` instead. -/
namespace Binary.Pair.Allowedips
open C1Split

theorem validate_allocate_valid {names : Names} {address : Nat}
    (valid : validate names Root.nodeOffsets=.ok ())
    (positive : 0<address) (aligned : address%8=0)
    (extent : address+Root.nodeOffsets.nodeSize<2^64)
    (fresh : ∀ span ∈ allocations names Root.nodeOffsets,
      disjointRanges address Root.nodeOffsets.nodeSize span.1 span.2=true)
    (tableApart : disjointRanges address Root.nodeOffsets.nodeSize names.table
      AllowedipsMutationLayout.tableSize=true) :
    validate (names.allocated address) Root.nodeOffsets=.ok () := by
  let o := Root.nodeOffsets
  let n := names.allocated address
  have arena := arena_of_valid valid
  have layout : o.nodeSize=72 := rfl
  have counter := ids_below_counter valid
  have g := arena.geometry.allocate (Nat.le_of_lt extent) fresh
  have absent : ∀ pair ∈ names.trie.nodes, pair.2≠address := by
    intro pair member same
    have separated := fresh (pair.2,o.nodeSize) (node_allocation member)
    change disjointRanges address 72 pair.2 72=true at separated
    simp only [disjointRanges,Bool.or_eq_true,decide_eq_true_eq] at separated
    omega
  have nodeAddresses : (n.trie.nodes.map Prod.snd).Nodup := by
    simp only [n,Names.allocated,List.map_append,List.map_cons,List.map_nil,List.nodup_append]
    refine ⟨arena.addresses,by simp,?_⟩
    intro a member b singleton equal
    obtain ⟨pair,present,atAddress⟩ := List.mem_map.mp member
    have bEq : b=address := by simpa using singleton
    exact absent pair present (atAddress.trans (equal.trans bEq))
  have oldValid0 := valid
  unfold validate at oldValid0
  obtain ⟨_,trieValid0,_⟩ := bind_ok oldValid0
  have ranges := trie_validate_ranges trieValid0
  have peerUnique : (names.trie.peers.map Prod.snd).Nodup ∧ (names.trie.peers.map Prod.fst).Nodup := by
    have unique := trieValid0
    unfold Trie.validate at unique
    obtain ⟨_,unique⟩ := check_ok _ _ _ _ unique
    obtain ⟨_,unique,_⟩ := bind_ok unique
    have all := forIn_ok
      (P := fun pairs : List (Nat×Nat) => (pairs.map Prod.snd).Nodup ∧ (pairs.map Prod.fst).Nodup)
      (fun pairs _ _ _ run => by
        obtain ⟨checked,run⟩ := check_ok _ _ _ _ run
        have lengths : (pairs.map Prod.fst).eraseDups.length=pairs.length ∧
            (pairs.map Prod.snd).eraseDups.length=pairs.length := by simpa using checked
        exact ⟨(),(Except.ok.inj run).symm,nodup_of_eraseDups_length _ (by simpa using lengths.2),
          nodup_of_eraseDups_length _ (by simpa using lengths.1)⟩) unique
    exact all names.trie.peers (by simp)
  have oldValid := valid
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
        exact ranges _ (node_allocation (id:=id) named)
      · obtain ⟨⟨id,base⟩,named,rfl⟩ := List.mem_map.mp peer
        exact ranges _ (List.mem_append_right _ (List.mem_map.mpr ⟨(id,base),named,rfl⟩))
    · exact ⟨positive,extent⟩
  have newTrie : Trie.validate n.trie o=.ok () := by
    unfold Trie.validate at trieValid
    obtain ⟨layoutCheck,_⟩ := check_ok _ _ _ _ trieValid
    apply trie_validate_construct layoutCheck _ allBounded g.apart
    intro pairs member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    · exact ⟨allocated_ids address arena.ids counter,nodeAddresses⟩
    · exact ⟨peerUnique.2,peerUnique.1⟩
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

#print axioms validate_allocate_valid
end Binary.Pair.Allowedips
