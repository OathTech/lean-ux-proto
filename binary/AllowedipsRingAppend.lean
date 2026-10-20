import AllowedipsRingAppendMemory

namespace Binary.Pair.Allowedips.Ring
open Index (skip)

theorem Chain.last_origin {names m head previous nodes last}
    (shape : Chain names m head previous nodes)
    (back : word m "peer.list.prev" (head+8) 8=.ok last) :
    last=previous ∨ last ∈ nodes.map Prod.fst := by
  induction shape with
  | nil close => exact .inl (word_values back close)
  | @cons previous link id rest fields tail ih =>
    rcases ih with equal|member
    · exact .inr (by simp [equal])
    · exact .inr (by simp [member])

theorem Chain.tail_iff {names m head nodes last link p q id}
    (shape : Chain names m head head nodes) (member : (link,id) ∈ nodes)
    (fields : Fields names m head p link q id)
    (enter : word m "peer.list.head" head 8=.ok (first head nodes))
    (back : word m "peer.list.prev" (head+8) 8=.ok last) : q=head ↔ link=last := by
  constructor
  · intro equal
    have next := shape.successor_read member fields
    rw [equal] at next
    exact word_values next back
  · intro equal
    have forward := shape.last_forward (Binary.Pair.word_path enter _) back
    rw [←equal] at forward
    exact word_values fields.forward forward

theorem Chain.head_tail_iff {names m head nodes last}
    (shape : Chain names m head head nodes)
    (enter : word m "peer.list.head" head 8=.ok (first head nodes))
    (back : word m "peer.list.prev" (head+8) 8=.ok last) : head=last ↔ first head nodes=head := by
  constructor
  · intro equal
    have forward := shape.last_forward (Binary.Pair.word_path enter _) back
    rw [←equal] at forward
    exact word_values enter forward
  · intro equal
    cases shape with
    | nil close => exact word_values close back
    | cons fields tail => exact False.elim (fields.notHead equal)

theorem Chain.append_fields {names o m head nodes last added addedId link p q id p' q'}
    (g : Geometry names o) (layout : o.nodeSize=72)
    (headSlot : LinkSlot names head) (lastSlot : LinkSlot names last)
    (shape : Chain names m head head nodes) (member : (link,id) ∈ nodes)
    (fields : Fields names m head p link q id) (focus : Fields names m head p' added q' addedId)
    (fresh : added ∉ nodes.map Prod.fst)
    (enter : word m "peer.list.head" head 8=.ok (first head nodes))
    (back : word m "peer.list.prev" (head+8) 8=.ok last) :
    Fields names (appendMemory m head last added) head p link (skip head added q) id := by
  have ne : link≠added := by intro equal; exact fresh (List.mem_map.mpr ⟨(link,id),member,equal⟩)
  have same := shape.tail_iff member fields enter back
  refine ⟨fields.known,fields.notHead,fields.valid,fields.owner,?_,?_⟩
  · rw [append_back g layout headSlot lastSlot focus.slot fields.slot]
    simp only [ne,fields.notHead,ite_false,fields.back]
  · rw [append_forward g layout headSlot lastSlot focus.slot fields.slot]
    simp only [←same,ne,ite_false,fields.forward,skip]
    split <;> rfl

theorem append_decodes {names o m head fuel entries last added id p q}
    (g : Geometry names o) (layout : o.nodeSize=72)
    (headSlot : LinkSlot names head) (lastSlot : LinkSlot names last)
    (focus : Fields names m head p added q id)
    (back : word m "peer.list.prev" (head+8) 8=.ok last)
    (decoded : (do
      let first ← word m "peer.list.head" head 8
      peerList names m head fuel first head [])=.ok entries)
    (fresh : id ∉ entries) (unique : (names.trie.nodes.map Prod.fst).Nodup)
    (budget : entries.length+1<fuel) :
    (do
      let first ← word (appendMemory m head last added) "peer.list.head" head 8
      peerList names (appendMemory m head last added) head fuel first head [])=.ok (entries++[id]) := by
  obtain ⟨firstWord,headRead,run⟩ := bind_ok decoded
  obtain ⟨nodes,entriesEq,headEq,shape,_,distinct,_⟩ := peerList_shape run
  have enter : word m "peer.list.head" head 8=.ok (first head nodes) := by simpa only [headEq] using headRead
  have absent : added ∉ nodes.map Prod.fst := by
    intro present
    obtain ⟨⟨link,current⟩,member,equal⟩ := List.mem_map.mp present
    obtain ⟨p,q,fields⟩ := shape.member_fields member
    have identity := (fields.identity_iff focus unique).mpr equal
    exact fresh (entriesEq ▸ List.mem_map.mpr ⟨(link,current),member,identity⟩)
  have notLast : added≠last := by
    intro equal
    rcases shape.last_origin back with root|member
    · exact focus.notHead (equal.trans root)
    · exact absent (equal ▸ member)
  have sentinel : word (appendMemory m head last added) "peer.list.prev" (head+8) 8=.ok added := by
    rw [append_back g layout headSlot lastSlot focus.slot headSlot]
    simp only [Ne.symm focus.notHead,ite_false,ite_true]
  have changed := shape.append sentinel (by
    intro previous previousRead
    have equal := word_values previousRead back
    refine ⟨focus.known,focus.notHead,focus.valid,focus.owner,?_,?_⟩
    · rw [append_back g layout headSlot lastSlot focus.slot focus.slot]
      simp only [ite_true,equal]
    · rw [append_forward g layout headSlot lastSlot focus.slot focus.slot]
      simp only [notLast,ite_false,ite_true])
    (fun link current p q member fields => shape.append_fields g layout headSlot lastSlot member fields focus absent enter back)
  have nd : ((nodes++[(added,id)]).map Prod.fst).Nodup := by
    simp only [List.map_append,List.map_cons,List.map_nil,List.nodup_append]
    refine ⟨distinct,by simp,?_⟩
    intro a member b singleton equal
    have bEq : b=added := by simpa using singleton
    exact absent ((equal.trans bEq) ▸ member)
  have result := changed.decode fuel [] (by simpa only [List.length_append,List.length_cons,List.length_nil,
      entriesEq,List.length_map] using budget) nd (by simp)
  rw [shape.first_append] at result
  have firstRead : word (appendMemory m head last added) "peer.list.head" head 8=
      .ok (skip head added (first head nodes)) := by
    rw [append_forward g layout headSlot lastSlot focus.slot headSlot]
    simp only [Ne.symm focus.notHead,ite_false,shape.head_tail_iff enter back,enter,skip]
    split <;> rfl
  rw [firstRead]
  change peerList names (appendMemory m head last added) head fuel
    (skip head added (first head nodes)) head []=_
  simpa only [List.map_append,List.map_cons,List.map_nil,←entriesEq] using result

#print axioms append_decodes
end Binary.Pair.Allowedips.Ring
