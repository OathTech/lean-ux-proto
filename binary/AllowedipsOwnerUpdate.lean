import AllowedipsRecordFrame

namespace Binary.Pair.Allowedips
open Leanux Leanux.WG

private theorem ok_bind (value : α) (f : α → Except ε β) :
    ((Except.ok value : Except ε α) >>= f)=f value := rfl

theorem core_owner_update {names o m d id base current address node pid peer}
    (related : Corresponds names o m d) (named : (id,base) ∈ names.trie.nodes)
    (currentNamed : (current,address) ∈ names.trie.nodes) (peerNamed : (pid,peer) ∈ names.trie.peers)
    (read : Trie.decodeNode names.trie o m address=.ok node) :
    Trie.decodeNode names.trie o (write64 m base peer) address=
      .ok (if current=id then {node with peer := some pid} else node) := by
  have core := Trie.reconstruct_fields related.trie
  by_cases equal : current=id
  · subst current
    have addresses := Index.unique_first core.nodeIds currentNamed named
    subst address
    simp only [ite_true]
    apply Trie.DecodedFields.decode
    apply (Trie.decodeNode_fields read).change_peer
    · refine ⟨peer,?_,?_⟩
      · have po : o.peer=0 := core.layout.2.1
        rw [po,Nat.add_zero]
        apply word_write64_same
        · have bound := (core.nodeRange id base named).2
          have layout : o.nodeSize=72 := core.layout.1
          rw [layout] at bound
          omega
        · have bound := (core.peerRange pid peer peerNamed).2
          omega
      · exact pointer_named (name_addresses related).2 peerNamed (core.peerRange pid peer peerNamed).1 _
    · intro offset size field different path
      have bounds := node_field_bounds related field
      exact node_owner_frame related named named bounds.1 (.inr (bounds.2.resolve_left different)) path
    · rcases core.layout with ⟨_,po,ch,ci,ba,bb,bl,bi,_⟩
      simp [po,ch,ci,ba,bb,bl,bi,AllowedipsLayout.peer,AllowedipsLayout.bit,AllowedipsLayout.cidr,
        AllowedipsLayout.bit_at_a,AllowedipsLayout.bit_at_b,AllowedipsLayout.bitlen,AllowedipsLayout.bits]
  · rw [ite_eq_right equal]
    have same : Trie.decodeNode names.trie o (write64 m base peer) address=Trie.decodeNode names.trie o m address := by
      apply Trie.decodeNode_congr
      intro offset size field path
      exact node_owner_frame related currentNamed named (node_field_bounds related field).1 (.inl equal) path
    exact same.trans read

theorem decodeNode_change_core {names o before after id base node nextPeer}
    (read : decodeNode names o before id base=.ok (id,node))
    (changed : Trie.decodeNode names.trie o after base=.ok {Trie.targetNode node with peer := nextPeer})
    (parentRead : word after "node.parent" (base+AllowedipsMutationLayout.parent_bit_packed) 8=
      word before "node.parent" (base+AllowedipsMutationLayout.parent_bit_packed) 8) :
    decodeNode names o after id base=.ok (id,{node with peer := nextPeer}) := by
  unfold decodeNode at read
  obtain ⟨old,_,read⟩ := bind_ok read
  obtain ⟨raw,rawRead,read⟩ := bind_ok read
  obtain ⟨slot,parent,read⟩ := bind_ok read
  cases Except.ok.inj read
  simp only [decodeNode,changed,parentRead,rawRead,parent,ok_bind]
  rfl

theorem owner_update {names o m d id base current address node pid peer}
    (related : Corresponds names o m d) (named : (id,base) ∈ names.trie.nodes)
    (currentNamed : (current,address) ∈ names.trie.nodes) (peerNamed : (pid,peer) ∈ names.trie.peers)
    (read : decodeNode names o m current address=.ok (current,node)) :
    decodeNode names o (write64 m base peer) current address=
      .ok (current,if current=id then {node with peer := some pid} else node) := by
  have coreRead := (decodeNode_fields read).2
  have changed := core_owner_update related named currentNamed peerNamed coreRead
  have parentRead := node_owner_frame (m:=m) (value:=peer) related currentNamed named
    (offset:=AllowedipsMutationLayout.parent_bit_packed) (size:=8) (by decide) (.inr (by decide)) "node.parent"
  by_cases equal : current=id
  · simp only [equal,ite_true] at changed ⊢
    simpa only [equal] using decodeNode_change_core read changed parentRead
  · rw [ite_eq_right equal] at changed ⊢
    have keep := decodeNode_change_core read changed parentRead
    simpa only using keep

#print axioms owner_update
end Binary.Pair.Allowedips
