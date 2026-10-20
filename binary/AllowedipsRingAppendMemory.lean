import AllowedipsRingUnlink

namespace Binary.Pair.Allowedips.Ring

/-- The four stores of list_add_tail, in the image's order. The tail is the
one read after any unlink, so no inequality between head and last is needed. -/
def appendMemory (m : DataMem) (head last added : Nat) : DataMem :=
  write64 (write64 (write64 (write64 m (head+8) added) added head) (added+8) last) last added

theorem append_forward {names o m head last added link}
    (g : Geometry names o) (layout : o.nodeSize=72)
    (h : LinkSlot names head) (t : LinkSlot names last) (n : LinkSlot names added)
    (r : LinkSlot names link) (path : String) :
    word (appendMemory m head last added) path link 8=
      if link=last then .ok added else if link=added then .ok head else word m path link 8 := by
  have rs : WordSlot names o link := by simpa only [Nat.add_zero] using r.word layout 0 (.inl rfl)
  have ts : WordSlot names o last := by simpa only [Nat.add_zero] using t.word layout 0 (.inl rfl)
  have ns : WordSlot names o added := by simpa only [Nat.add_zero] using n.word layout 0 (.inl rfl)
  unfold appendMemory
  rw [word_write64 _ path link last added (rs.bounded g) (link_bound n g layout) (rs.disjoint ts g)]
  rw [word_write64_frame _ path link 8 (added+8) last (r.forward_back_apart n g layout)]
  rw [word_write64 _ path link added head (rs.bounded g) (link_bound h g layout) (rs.disjoint ns g)]
  rw [word_write64_frame _ path link 8 (head+8) added (r.forward_back_apart h g layout)]

theorem append_back {names o m head last added link}
    (g : Geometry names o) (layout : o.nodeSize=72)
    (h : LinkSlot names head) (t : LinkSlot names last) (n : LinkSlot names added)
    (r : LinkSlot names link) (path : String) :
    word (appendMemory m head last added) path (link+8) 8=
      if link=added then .ok last else if link=head then .ok added else word m path (link+8) 8 := by
  have rb := r.word layout 8 (.inr rfl)
  have nb := n.word layout 8 (.inr rfl)
  have hb := h.word layout 8 (.inr rfl)
  unfold appendMemory
  rw [word_write64_frame _ path (link+8) 8 last added (by
    intro a back forward; exact t.forward_back_apart r g layout a forward back)]
  rw [word_write64 _ path (link+8) (added+8) last (rb.bounded g) (link_bound t g layout) (rb.disjoint nb g)]
  rw [word_write64_frame _ path (link+8) 8 added head (by
    intro a back forward; exact n.forward_back_apart r g layout a forward back)]
  rw [word_write64 _ path (link+8) (head+8) added (rb.bounded g) (link_bound n g layout) (rb.disjoint hb g)]
  simp only [Nat.add_right_cancel_iff]

#print axioms append_forward
#print axioms append_back
end Binary.Pair.Allowedips.Ring
