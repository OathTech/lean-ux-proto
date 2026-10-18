import PairBucketErase

namespace Binary.Pair.Index
open Leanux Leanux.WG

theorem Chain.head_back {n o m b fieldB previous nodes link oldPrevious oldNext entry}
    (shape : Chain n o m b previous nodes)
    (fields : NodeFields n o m fieldB link oldPrevious oldNext entry)
    (atHead : head nodes=link) : previous=oldPrevious := by
  cases shape with
  | nil => exact False.elim (fields.nonzero atHead.symm)
  | cons first tail =>
    change _=link at atHead
    subst link
    exact word_values first.back fields.back

theorem Chain.member_fields {n o m b previous nodes link entry}
    (shape : Chain n o m b previous nodes) (member : (link,entry) ∈ nodes) :
    ∃ prev next, NodeFields n o m b link prev next entry := by
  induction shape with
  | nil => cases member
  | cons first tail ih =>
    rcases List.mem_cons.mp member with equal | member
    · cases equal
      exact ⟨_,_,first⟩
    · exact ih member

theorem Chain.head_zero {n o m b previous nodes}
    (shape : Chain n o m b previous nodes) : head nodes=0 ↔ nodes=[] := by
  cases shape with
  | nil => simp [head]
  | cons fields tail => simp [head,fields.nonzero]

/-- A node's predecessor is either the bucket head or a node in this
chain. This excludes arbitrary writable predecessor pointers without
introducing a second heap invariant. -/
theorem Chain.back_origin {n o m b fieldB previous nodes link oldPrevious oldNext entry}
    (shape : Chain n o m b previous nodes) (member : (link,entry) ∈ nodes)
    (fields : NodeFields n o m fieldB link oldPrevious oldNext entry) :
    (oldPrevious=previous ∧ link=head nodes) ∨
      ∃ parent current prev, (parent,current) ∈ nodes ∧
        parent+o.next=oldPrevious ∧ NodeFields n o m b parent prev link current := by
  induction shape with
  | nil => cases member
  | @cons previous first current rest firstFields tail ih =>
    rcases List.mem_cons.mp member with equal | member
    · cases equal
      exact .inl ⟨word_values fields.back firstFields.back,rfl⟩
    · rcases ih member with ⟨prev,atHead⟩ | ⟨parent,current,prev,parentMem,address,parentFields⟩
      · exact .inr ⟨first,current,previous,by simp,prev.symm,by simpa only [atHead] using firstFields⟩
      · exact .inr ⟨parent,current,prev,List.mem_cons_of_mem _ parentMem,address,parentFields⟩

theorem Chain.predecessor_read {n o m b fieldB root nodes link previous next entry}
    (shape : Chain n o m b root nodes) (member : (link,entry) ∈ nodes)
    (fields : NodeFields n o m fieldB link previous next entry)
    (rootRead : word m "bucket.head" root 8=.ok (head nodes)) :
    word m "unlink.predecessor" previous 8=.ok link := by
  rcases shape.back_origin member fields with ⟨atRoot,atHead⟩ | ⟨parent,current,prev,_,address,parentFields⟩
  · rw [atRoot,atHead]
    exact word_path rootRead _
  · rw [←address]
    exact word_path parentFields.forward _

theorem Chain.forward_to {n o m b fieldB focusB previous nodes link oldPrevious oldNext entry removed removedPrevious removedNext focusEntry}
    (shape : Chain n o m b previous nodes) (member : (link,entry) ∈ nodes)
    (fields : NodeFields n o m fieldB link oldPrevious oldNext entry)
    (focus : NodeFields n o m focusB removed removedPrevious removedNext focusEntry)
    (points : oldNext=removed) : link+o.next=removedPrevious := by
  induction shape with
  | nil => cases member
  | cons first tail ih =>
    rcases List.mem_cons.mp member with equal | member
    · cases equal
      have next := word_values first.forward fields.forward
      exact tail.head_back focus (next.trans points)
    · exact ih member

theorem Chain.back_from {n o m b fieldB focusB previous nodes link oldPrevious oldNext entry removed removedPrevious removedNext focusEntry}
    (shape : Chain n o m b previous nodes) (member : (link,entry) ∈ nodes)
    (fields : NodeFields n o m fieldB link oldPrevious oldNext entry)
    (focus : NodeFields n o m focusB removed removedPrevious removedNext focusEntry)
    (rootApart : previous≠removed+o.next)
    (points : oldPrevious=removed+o.next) : link=removedNext := by
  rcases shape.back_origin member fields with ⟨root,_⟩ | ⟨parent,current,prev,_,address,parentFields⟩
  · exact False.elim (rootApart (root.symm.trans points))
  · have same : parent=removed := by omega
    subst parent
    exact word_values parentFields.forward focus.forward

theorem Chain.successor {n o m b fieldB previous nodes link oldPrevious oldNext entry}
    (shape : Chain n o m b previous nodes) (member : (link,entry) ∈ nodes)
    (fields : NodeFields n o m fieldB link oldPrevious oldNext entry)
    (nonzero : oldNext≠0) :
    ∃ current next, NodeFields n o m b oldNext (link+o.next) next current := by
  induction shape with
  | nil => cases member
  | cons first tail ih =>
    rcases List.mem_cons.mp member with equal | member
    · cases equal
      have next := word_values first.forward fields.forward
      cases tail with
      | nil => exact False.elim (nonzero next.symm)
      | cons successor rest =>
        change _=oldNext at next
        subst oldNext
        exact ⟨_,_,successor⟩
    · exact ih member

/-- Pointer-value changes correspond to the actual addresses of the two
neighbour stores. The reverse directions use the original stored words. -/
theorem Chain.neighbor_addresses
    {n o m b focusB root nodes focusRoot focusNodes link oldPrevious oldNext entry removed removedPrevious removedNext focusEntry}
    (shape : Chain n o m b root nodes) (member : (link,entry) ∈ nodes)
    (fields : NodeFields n o m b link oldPrevious oldNext entry)
    (focusShape : Chain n o m focusB focusRoot focusNodes)
    (focusMember : (removed,focusEntry) ∈ focusNodes)
    (focus : NodeFields n o m focusB removed removedPrevious removedNext focusEntry)
    (rootApart : root≠removed+o.next)
    (predecessor : word m "unlink.predecessor" removedPrevious 8=.ok removed) :
    (oldNext=removed ↔ link+o.next=removedPrevious) ∧
    (oldPrevious=removed+o.next ↔ link=removedNext) := by
  constructor
  · constructor
    · exact shape.forward_to member fields focus
    · intro address
      have read := fields.forward
      rw [address] at read
      exact word_values read predecessor
  · constructor
    · exact shape.back_from member fields focus rootApart
    · intro address
      have nonzero : removedNext≠0 := address ▸ fields.nonzero
      obtain ⟨current,next,successor⟩ := focusShape.successor focusMember focus nonzero
      have read := fields.back
      rw [address] at read
      exact word_values read successor.back

#print axioms Chain.back_origin
#print axioms Chain.forward_to
#print axioms Chain.back_from
end Binary.Pair.Index
