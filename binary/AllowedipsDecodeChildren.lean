import AllowedipsDecodeConstruct

namespace Binary.Pair.Trie

/-- Update the two reconstructed child fields while framing the rest of the
record. This is shared by child, covering and intermediate-node insertion. -/
theorem DecodedFields.change_children {names o before after base node left right}
    (fields : DecodedFields names o before base node)
    (changed : ∃ lp rp,
      word after "node.child[0]" (base+o.children) 8=.ok lp ∧
      pointer names.nodes "node.child[0]" lp=.ok left ∧
      word after "node.child[1]" (base+o.children+8) 8=.ok rp ∧
      pointer names.nodes "node.child[1]" rp=.ok right)
    (same : ∀ offset size, (offset,size) ∈ nodeSpans o → offset≠o.children → offset≠o.children+8 → ∀ path,
      word after path (base+offset) size=word before path (base+offset) size)
    (separate : ∀ offset ∈ [o.peer,o.cidr,o.bitlen,o.bitAtA,o.bitAtB,o.bits,o.bits+8],
      offset≠o.children ∧ offset≠o.children+8) :
    DecodedFields names o after base {node with children:=#[left,right]} := by
  have keep (offset size : Nat) (field : (offset,size) ∈ nodeSpans o)
      (member : offset ∈ [o.peer,o.cidr,o.bitlen,o.bitAtA,o.bitAtB,o.bits,o.bits+8]) (path : String) :=
    same offset size field (separate offset member).1 (separate offset member).2 path
  refine ⟨?_,?_,?_,?_,fields.family,fields.bounded,?_,?_,?_⟩
  · obtain ⟨peer,read,decoded⟩ := fields.peer
    exact ⟨peer,(keep _ 8 (by simp [nodeSpans]) (by simp) _).trans read,decoded⟩
  · obtain ⟨lp,rp,leftRead,leftDecoded,rightRead,rightDecoded⟩ := changed
    exact ⟨left,right,lp,rp,rfl,leftRead,leftDecoded,rightRead,rightDecoded⟩
  · rw [keep _ 1 (by simp [nodeSpans]) (by simp) _]; exact fields.cidr
  · rw [keep _ 1 (by simp [nodeSpans]) (by simp) _]; exact fields.width
  · rw [keep _ 1 (by simp [nodeSpans]) (by simp) _]; exact fields.byteSelector
  · rw [keep _ 1 (by simp [nodeSpans]) (by simp) _]; exact fields.bitSelector
  · dsimp only
    split
    · rename_i family
      rw [keep _ 4 (by simp [nodeSpans]) (by simp) _]
      simpa only [family,ite_true] using fields.key
    · rename_i family
      obtain ⟨hi,lo,hiRead,loRead,value⟩ := (ite_eq_right family ▸ fields.key)
      refine ⟨hi,lo,?_,?_,value⟩
      · rw [keep _ 8 (by simp [nodeSpans]) (by simp) _]; exact hiRead
      · rw [Nat.add_assoc,keep _ 8 (by simp [nodeSpans]) (by simp) _]; exact loRead

#print axioms DecodedFields.change_children
end Binary.Pair.Trie
