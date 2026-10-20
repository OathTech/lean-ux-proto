import AllowedipsListFrame

namespace Binary.Pair.Trie

private theorem ok_bind (value : α) (f : α → Except ε β) :
    ((Except.ok value : Except ε α) >>= f)=f value := rfl

/-- Rebuild the executable record decoder from its extracted field facts.
Mutation proofs update those facts instead of repeatedly unfolding the whole
decoder through a byte-store chain. -/
theorem DecodedFields.decode {names o m base node} (fields : DecodedFields names o m base node) :
    decodeNode names o m base=.ok node := by
  obtain ⟨peer,peerRead,peerDecode⟩ := fields.peer
  obtain ⟨left,right,lp,rp,children,leftRead,leftDecode,rightRead,rightDecode⟩ := fields.children
  have family : ((node.width==32 || node.width==128) && decide (node.cidr≤node.width))=true := by
    simpa only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] using And.intro fields.family fields.bounded
  simp only [decodeNode,Std.Legacy.Range.forIn_eq_forIn_range',
    show ([:2] : Std.Legacy.Range).size=2 from rfl,
    List.range'_succ,List.range'_zero,List.forIn_cons,List.forIn_nil,
    Nat.reduceAdd,Nat.reduceMul,Nat.add_zero,bind_assoc,pure_bind]
  simp only [show toString ("node.child[" : String)="node.child[" from rfl,
    show toString ("]" : String)="]" from rfl,
    peerRead,peerDecode,leftRead,leftDecode,rightRead,rightDecode,ok_bind,
    fields.cidr,fields.width,family,ite_true,
    fields.byteSelector,fields.bitSelector,beq_self_eq_true,Bool.and_self]
  by_cases width : node.width=32
  · have key := fields.key
    simp only [width,ite_true] at key
    simp only [width,beq_self_eq_true,ite_true,key,ok_bind]
    cases node
    cases children
    cases width
    rfl
  · have key := fields.key
    rw [ite_eq_right width] at key
    obtain ⟨hi,lo,highRead,lowRead,keyEq⟩ := key
    simp only [show (node.width==32)=false from by simp [width],Bool.false_eq_true,ite_false,highRead,lowRead,ok_bind]
    cases node
    cases children
    cases keyEq
    rfl

theorem DecodedFields.change_peer {names o before after base node peer}
    (fields : DecodedFields names o before base node)
    (changed : ∃ raw, word after "node.peer" (base+o.peer) 8=.ok raw ∧
      pointer names.peers "node.peer" raw=.ok peer)
    (same : ∀ offset size, (offset,size) ∈ nodeSpans o → offset≠o.peer → ∀ path,
      word after path (base+offset) size=word before path (base+offset) size)
    (separate : o.children≠o.peer ∧ o.children+8≠o.peer ∧ o.cidr≠o.peer ∧ o.bitlen≠o.peer ∧
      o.bitAtA≠o.peer ∧ o.bitAtB≠o.peer ∧ o.bits≠o.peer ∧ o.bits+8≠o.peer) :
    DecodedFields names o after base {node with peer} := by
  rcases separate with ⟨c0,c1,cidr,width,byte,bit,key,low⟩
  refine ⟨changed,?_,?_,?_,fields.family,fields.bounded,?_,?_,?_⟩
  · obtain ⟨left,right,lp,rp,children,leftRead,leftDecode,rightRead,rightDecode⟩ := fields.children
    refine ⟨left,right,lp,rp,children,?_,leftDecode,?_,rightDecode⟩
    · rw [same _ _ (by simp [nodeSpans]) c0]; exact leftRead
    · rw [Nat.add_assoc,same _ 8 (by simp [nodeSpans]) c1]; exact rightRead
  · rw [same _ _ (by simp [nodeSpans]) cidr]; exact fields.cidr
  · rw [same _ _ (by simp [nodeSpans]) width]; exact fields.width
  · rw [same _ _ (by simp [nodeSpans]) byte]; exact fields.byteSelector
  · rw [same _ _ (by simp [nodeSpans]) bit]; exact fields.bitSelector
  · dsimp only
    split
    · rename_i family
      rw [same _ _ (by simp [nodeSpans]) key]
      simpa only [family,ite_true] using fields.key
    · rename_i family
      obtain ⟨hi,lo,hiRead,loRead,value⟩ := (ite_eq_right family ▸ fields.key)
      refine ⟨hi,lo,?_,?_,value⟩
      · rw [same _ _ (by simp [nodeSpans]) key]; exact hiRead
      · rw [Nat.add_assoc,same _ 8 (by simp [nodeSpans]) low]; exact loRead

#print axioms DecodedFields.decode
end Binary.Pair.Trie
