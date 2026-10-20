import AllowedipsLinkSlots
import PairWordWrites

namespace Binary.Pair.Allowedips.Ring

/-- Actual list_del store order, without poisoning the detached node. -/
def unlinkMemory (m : DataMem) (previous next : Nat) : DataMem :=
  write64 (write64 m (next+8) previous) previous next

theorem link_bound {names o link} (slot : LinkSlot names link) (g : Geometry names o) (layout : o.nodeSize=72) :
    link<2^64 := by
  have h := (slot.word layout 0 (.inl rfl)).bounded g
  omega

theorem unlink_forward {names o m previous next link}
    (g : Geometry names o) (layout : o.nodeSize=72)
    (p : LinkSlot names previous) (q : LinkSlot names next) (r : LinkSlot names link) (path : String) :
    word (unlinkMemory m previous next) path link 8=
      if link=previous then .ok next else word m path link 8 := by
  have rs : WordSlot names o link := by simpa only [Nat.add_zero] using r.word layout 0 (.inl rfl)
  have ps : WordSlot names o previous := by simpa only [Nat.add_zero] using p.word layout 0 (.inl rfl)
  unfold unlinkMemory
  rw [word_write64 _ path link previous next (rs.bounded g) (link_bound q g layout) (rs.disjoint ps g)]
  rw [word_write64_frame _ path link 8 (next+8) previous (r.forward_back_apart q g layout)]

theorem unlink_back {names o m previous next link}
    (g : Geometry names o) (layout : o.nodeSize=72)
    (p : LinkSlot names previous) (q : LinkSlot names next) (r : LinkSlot names link) (path : String) :
    word (unlinkMemory m previous next) path (link+8) 8=
      if link=next then .ok previous else word m path (link+8) 8 := by
  have rb := r.word layout 8 (.inr rfl)
  have qb := q.word layout 8 (.inr rfl)
  unfold unlinkMemory
  rw [word_write64_frame _ path (link+8) 8 previous next (by
    intro a back forward
    exact p.forward_back_apart r g layout a forward back)]
  rw [word_write64 _ path (link+8) (next+8) previous (rb.bounded g) (link_bound p g layout) (rb.disjoint qb g)]
  simp only [Nat.add_right_cancel_iff]

/-- An exact reassignment's peer-word update leaves all circular-list words
unchanged, even when the focus is currently an internal self-linked node. -/
theorem owner_word_frame {names o m link id base value}
    (g : Geometry names o) (layout : o.nodeSize=72) (r : LinkSlot names link)
    (owner : (id,base) ∈ names.trie.nodes) (offset : Nat) (which : offset=0 ∨ offset=8) (path : String) :
    word (write64 m base value) path (link+offset) 8=word m path (link+offset) 8 :=
  word_write64_frame m path (link+offset) 8 base value (r.owner_apart owner g layout offset which)

#print axioms unlink_forward
#print axioms unlink_back
end Binary.Pair.Allowedips.Ring
