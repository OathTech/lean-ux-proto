import PairAllowedipsReadSet

namespace Binary.Pair.Allowedips
open Leanux Leanux.WG


theorem peerList_congr (names : Names) (before after : DataMem) (head : Nat)
    (headRead : ∀ path offset, offset=0 ∨ offset=8 →
      word before path (head+offset) 8=word after path (head+offset) 8)
    (nodeRead : ∀ id a, (id,a) ∈ names.trie.nodes → ∀ path offset, offset=0 ∨ offset=8 →
      word before path (a+AllowedipsMutationLayout.peer_list+offset) 8=
        word after path (a+AllowedipsMutationLayout.peer_list+offset) 8)
    (fuel link previous : Nat) (seen : List Nat) :
    peerList names before head fuel link previous seen=peerList names after head fuel link previous seen := by
  induction fuel generalizing link previous seen with
  | zero => rfl
  | succ fuel ih =>
    have reads (known : (link == head || names.trie.nodes.any
        (fun (_,a) => link == a+AllowedipsMutationLayout.peer_list))=true)
        (path : String) (offset : Nat) (which : offset=0 ∨ offset=8) :
        word before path (link+offset) 8=word after path (link+offset) 8 := by
      have alternatives : link=head ∨ ∃ id a, (id,a) ∈ names.trie.nodes ∧
          link=a+AllowedipsMutationLayout.peer_list := by simpa using known
      rcases alternatives with root | ⟨id,a,member,eq⟩
      · rw [root]
        exact headRead path offset which
      · rw [eq]
        exact nodeRead id a member path offset which
    by_cases known : (link == head || names.trie.nodes.any
        (fun (_,a) => link == a+AllowedipsMutationLayout.peer_list))=true
    · have prev := reads known "peer.list.prev" 8 (Or.inr rfl)
      have next := reads known "peer.list.next" 0 (Or.inl rfl)
      simp only [Nat.add_zero] at next
      simp only [peerList, known, Bool.not_true, Bool.false_eq_true, ↓reduceIte, prev, next, ih]
    · have rejected : (link == head || names.trie.nodes.any
          (fun (_,a) => link == a+AllowedipsMutationLayout.peer_list))=false := by simpa using known
      simp only [peerList, rejected, Bool.not_false, ↓reduceIte]

theorem reconstruct_congr (names : Names) (o : AllowedipsProbe.Offsets) (before after : DataMem)
    (table : ∀ offset ∈ [AllowedipsMutationLayout.root4,AllowedipsMutationLayout.root6,AllowedipsMutationLayout.seq],
      ∀ path, word before path (names.table+offset) 8=word after path (names.table+offset) 8)
    (nodes : ∀ id a, (id,a) ∈ names.trie.nodes →
      Trie.decodeNode names.trie o before a=Trie.decodeNode names.trie o after a)
    (parents : ∀ id a, (id,a) ∈ names.trie.nodes →
      word before "node.parent" (a+AllowedipsMutationLayout.parent_bit_packed) 8=
        word after "node.parent" (a+AllowedipsMutationLayout.parent_bit_packed) 8)
    (nodeLists : ∀ id a, (id,a) ∈ names.trie.nodes → ∀ path offset, offset=0 ∨ offset=8 →
      word before path (a+AllowedipsMutationLayout.peer_list+offset) 8=
        word after path (a+AllowedipsMutationLayout.peer_list+offset) 8)
    (counts : ∀ id a, (id,a) ∈ names.trie.peers →
      word before "peer.refcount" (a+o.peerRefcount) 4=word after "peer.refcount" (a+o.peerRefcount) 4)
    (heads : ∀ id a, (id,a) ∈ names.trie.peers → ∀ path offset, offset=0 ∨ offset=8 →
      word before path (a+AllowedipsMutationLayout.allowedips_list+offset) 8=
        word after path (a+AllowedipsMutationLayout.allowedips_list+offset) 8) :
    reconstruct names o before=reconstruct names o after := by
  have ns : names.trie.nodes.mapM (fun (id,a) => decodeNode names o before id a)=
      names.trie.nodes.mapM (fun (id,a) => decodeNode names o after id a) := by
    apply Trie.mapM_same
    rintro ⟨id,a⟩ member
    simp only [decodeNode,nodes id a member,parents id a member]
  have ps : names.trie.peers.mapM (fun (id,a) => decodePeer names o before id a)=
      names.trie.peers.mapM (fun (id,a) => decodePeer names o after id a) := by
    apply Trie.mapM_same
    rintro ⟨id,a⟩ member
    have first := heads id a member "peer.list.head" 0 (Or.inl rfl)
    simp only [Nat.add_zero] at first
    simp only [decodePeer,counts id a member,first,
      peerList_congr names before after _ (heads id a member) nodeLists]
  simp only [reconstruct,ns,ps,table AllowedipsMutationLayout.root4 (by simp) "table.root4",
    table AllowedipsMutationLayout.root6 (by simp) "table.root6",table AllowedipsMutationLayout.seq (by simp) "table.seq"]

theorem reconstruct_frame {before after : DataMem} {writes : BitVec 64 → Prop}
    (names : Names) (o : AllowedipsProbe.Offsets)
    (same : EqualOutside writes before after)
    (apart : ∀ span ∈ readSpans names o, ∀ a, span.contains a → ¬writes a) :
    reconstruct names o before=reconstruct names o after := by
  have wordSame (base size : Nat) (member : (base,size) ∈ readSpans names o) (path : String) :
      word before path base size=word after path base size :=
    Trie.word_frame same path base size (apart _ member)
  have tableRead (offset size : Nat) (field : (offset,size) ∈ tableFields) (path : String) :=
    wordSame (names.table+offset) size
      (List.mem_append_left _ (List.mem_map.mpr ⟨(offset,size),field,rfl⟩)) path
  have nodeRead (id a offset size : Nat) (named : (id,a) ∈ names.trie.nodes)
      (field : (offset,size) ∈ nodeFields o) (path : String) :=
    wordSame (a+offset) size (List.mem_append_right _ (List.mem_append_left _
      (List.mem_flatMap.mpr ⟨(id,a),named,List.mem_map.mpr ⟨(offset,size),field,rfl⟩⟩))) path
  have peerRead (id a offset size : Nat) (named : (id,a) ∈ names.trie.peers)
      (field : (offset,size) ∈ peerFields o) (path : String) :=
    wordSame (a+offset) size (List.mem_append_right _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨(id,a),named,List.mem_map.mpr ⟨(offset,size),field,rfl⟩⟩))) path
  apply reconstruct_congr
  · intro offset field path
    apply tableRead offset 8 _ path
    simpa [tableFields] using field
  · intro id a named
    apply Trie.decodeNode_congr
    intro offset size field path
    exact nodeRead id a offset size named (List.mem_append_left _ field) path
  · intro id a named
    exact nodeRead id a _ 8 named (by simp [nodeFields]) _
  · intro id a named path offset which
    rcases which with rfl | rfl
    · simpa only [Nat.add_zero] using nodeRead id a AllowedipsMutationLayout.peer_list 8 named
        (by simp [nodeFields]) path
    · simpa only [Nat.add_assoc] using nodeRead id a (AllowedipsMutationLayout.peer_list+8) 8 named
        (by simp [nodeFields]) path
  · intro id a named
    exact peerRead id a o.peerRefcount 4 named (by simp [peerFields]) _
  · intro id a named path offset which
    rcases which with rfl | rfl
    · simpa only [Nat.add_zero] using peerRead id a AllowedipsMutationLayout.allowedips_list 8 named
        (by simp [peerFields]) path
    · simpa only [Nat.add_assoc] using peerRead id a (AllowedipsMutationLayout.allowedips_list+8) 8 named
        (by simp [peerFields]) path

#print axioms peerList_congr
#print axioms reconstruct_congr
#print axioms reconstruct_frame
end Binary.Pair.Allowedips
