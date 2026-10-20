import AllowedipsPeerListEdit

namespace Binary.Pair.Allowedips.Ring

theorem Chain.head_back {names m head previous nodes link oldPrev oldNext id}
    (shape : Chain names m head previous nodes) (fields : Fields names m head oldPrev link oldNext id)
    (atHead : first head nodes=link) : previous=oldPrev := by
  cases shape with
  | nil => exact False.elim (fields.notHead atHead.symm)
  | cons first tail =>
    change _=link at atHead
    subst link
    exact word_values first.back fields.back

theorem Chain.member_fields {names m head previous nodes link id}
    (shape : Chain names m head previous nodes) (member : (link,id) ∈ nodes) :
    ∃ p q, Fields names m head p link q id := by
  induction shape with
  | nil => cases member
  | cons fields tail ih =>
    rcases List.mem_cons.mp member with equal | member
    · cases equal; exact ⟨_,_,fields⟩
    · exact ih member

theorem Chain.back_origin {names m head previous nodes link oldPrev oldNext id}
    (shape : Chain names m head previous nodes) (member : (link,id) ∈ nodes)
    (fields : Fields names m head oldPrev link oldNext id) :
    (oldPrev=previous ∧ link=first head nodes) ∨
      ∃ parent current p, (parent,current) ∈ nodes ∧ parent=oldPrev ∧ Fields names m head p parent link current := by
  induction shape with
  | nil => cases member
  | @cons previous a current rest fs tail ih =>
    rcases List.mem_cons.mp member with equal | member
    · cases equal; exact .inl ⟨word_values fields.back fs.back,rfl⟩
    · rcases ih member with ⟨prev,atHead⟩ | ⟨parent,current,p,present,address,ps⟩
      · exact .inr ⟨a,current,previous,by simp,prev.symm,by simpa only [atHead] using fs⟩
      · exact .inr ⟨parent,current,p,List.mem_cons_of_mem _ present,address,ps⟩

theorem Chain.predecessor_read {names m head nodes link previous next id}
    (shape : Chain names m head head nodes) (member : (link,id) ∈ nodes)
    (fields : Fields names m head previous link next id)
    (headRead : word m "peer.list.head" head 8=.ok (first head nodes)) :
    word m "unlink.predecessor" previous 8=.ok link := by
  rcases shape.back_origin member fields with ⟨atRoot,atHead⟩ | ⟨parent,current,p,_,address,fs⟩
  · rw [atRoot,atHead]; exact word_path headRead _
  · rw [←address]; exact word_path fs.forward _

theorem Chain.successor_read {names m head previous nodes link oldPrev oldNext id}
    (shape : Chain names m head previous nodes) (member : (link,id) ∈ nodes)
    (fields : Fields names m head oldPrev link oldNext id) :
    word m "peer.list.prev" (oldNext+8) 8=.ok link := by
  induction shape with
  | nil => cases member
  | cons fs tail ih =>
    rcases List.mem_cons.mp member with equal | member
    · cases equal
      have next := word_values fs.forward fields.forward
      cases tail with
      | nil back => simpa only [←next,first,List.head?_nil,List.head?_cons,Option.map_none,Option.map_some,Option.getD_none,Option.getD_some] using back
      | cons child rest => simpa only [←next,first,List.head?_nil,List.head?_cons,Option.map_none,Option.map_some,Option.getD_none,Option.getD_some] using child.back
    · exact ih member

theorem Chain.forward_to {names m head previous nodes link p q id removed oldPrev oldNext focusId}
    (shape : Chain names m head previous nodes) (member : (link,id) ∈ nodes)
    (fields : Fields names m head p link q id) (focus : Fields names m head oldPrev removed oldNext focusId)
    (points : q=removed) : link=oldPrev := by
  induction shape with
  | nil => cases member
  | cons fs tail ih =>
    rcases List.mem_cons.mp member with equal | member
    · cases equal; exact tail.head_back focus ((word_values fs.forward fields.forward).trans points)
    · exact ih member

theorem Chain.back_from {names m head previous nodes link p q id removed oldPrev oldNext focusId}
    (shape : Chain names m head previous nodes) (member : (link,id) ∈ nodes)
    (fields : Fields names m head p link q id) (focus : Fields names m head oldPrev removed oldNext focusId)
    (rootApart : previous≠removed) (points : p=removed) : link=oldNext := by
  rcases shape.back_origin member fields with ⟨root,_⟩ | ⟨parent,current,prev,_,address,fs⟩
  · exact False.elim (rootApart (root.symm.trans points))
  · have same : parent=removed := address.trans points
    have read := fs.forward
    rw [same] at read
    exact word_values read focus.forward

/-- Backlink consistency supplies both directions, including a self-linked
internal node as the focus. No other peer's list may alias that node. -/
theorem Chain.neighbors {names m head nodes link p q id removed oldPrev oldNext focusId}
    (shape : Chain names m head head nodes) (member : (link,id) ∈ nodes)
    (fields : Fields names m head p link q id) (focus : Fields names m head oldPrev removed oldNext focusId)
    (predecessor : word m "unlink.predecessor" oldPrev 8=.ok removed)
    (successor : word m "peer.list.prev" (oldNext+8) 8=.ok removed) :
    (q=removed ↔ link=oldPrev) ∧ (p=removed ↔ link=oldNext) := by
  constructor
  · constructor
    · exact shape.forward_to member fields focus
    · intro address
      exact word_values (address ▸ fields.forward) predecessor
  · constructor
    · exact shape.back_from member fields focus (Ne.symm focus.notHead)
    · intro address
      exact word_values (address ▸ fields.back) successor

/-- The sentinel's backward word identifies a node whose forward word is the
sentinel. This also holds for an empty ring through the sentinel's own words. -/
theorem Chain.last_forward {names m head previous nodes last}
    (shape : Chain names m head previous nodes)
    (enter : word m "peer.list.next" previous 8=.ok (first head nodes))
    (back : word m "peer.list.prev" (head+8) 8=.ok last) :
    word m "peer.list.next" last 8=.ok head := by
  induction shape with
  | nil close =>
    have same := word_values close back
    subst last
    exact enter
  | cons fields tail ih => exact ih fields.forward

#print axioms Chain.neighbors
#print axioms Chain.last_forward
end Binary.Pair.Allowedips.Ring
