import AllowedipsNamesExtension
import AllowedipsDecodeConstruct

namespace Binary.Pair.Allowedips

theorem packed_root {slot : Nat} (aligned : slot%4=0) : slot ||| 2=slot+2 := by
  have low := Nat.or_mod_two_pow (a:=slot) (b:=2) (n:=2)
  have high := Nat.or_div_two_pow (a:=slot) (b:=2) (n:=2)
  simp only [Nat.reducePow,aligned,Nat.reduceMod,Nat.zero_or] at low
  simp only [Nat.reducePow,Nat.reduceDiv,Nat.or_zero] at high
  omega

theorem parent_root4 (names : Names) (aligned : names.table%8=0) :
    parent names ((names.table+AllowedipsMutationLayout.root4) ||| 2)=.ok .root4 := by
  have alignment : (names.table+AllowedipsMutationLayout.root4)%4=0 := by
    simp only [AllowedipsMutationLayout.root4,Nat.add_zero]; omega
  rw [packed_root alignment]
  have tag : (names.table+AllowedipsMutationLayout.root4+2)%4=2 := by omega
  simp only [parent,tag,beq_self_eq_true,ite_true,Nat.add_sub_cancel]
  rfl

theorem parent_root6 (names : Names) (aligned : names.table%8=0) :
    parent names ((names.table+AllowedipsMutationLayout.root6) ||| 2)=.ok .root6 := by
  have alignment : (names.table+AllowedipsMutationLayout.root6)%4=0 := by
    simp only [AllowedipsMutationLayout.root6]; omega
  rw [packed_root alignment]
  have tag : (names.table+AllowedipsMutationLayout.root6+2)%4=2 := by omega
  simp only [parent,tag,beq_self_eq_true,ite_true,Nat.add_sub_cancel]
  simp only [AllowedipsMutationLayout.root4,AllowedipsMutationLayout.root6,Nat.add_zero,
    show (names.table+8==names.table)=false from by simp]
  rfl

/-- Allocation extends names without changing any successfully decoded old
parent, including child pointers. No freshness restriction is needed for this
preservation fact; geometry validation separately checks new ownership. -/
theorem parent_allocate {names : Names} {raw address slot}
    (decoded : parent names raw=.ok slot) : parent (names.allocated address) raw=.ok slot := by
  simp only [parent,Names.allocated] at decoded ⊢
  split at decoded
  · rename_i root
    simp only [root,ite_true]
    split at decoded
    · rename_i at4; simpa only [at4,ite_true] using decoded
    · rename_i not4
      simp only [not4,Bool.false_eq_true,ite_false]
      split at decoded
      · rename_i at6; simpa only [at6,ite_true] using decoded
      · cases decoded
  · rename_i child
    simp only [child,Bool.false_eq_true,ite_false]
    split at decoded
    · rename_i valid
      simp only [valid,ite_true]
      obtain ⟨p,read,decoded⟩ := bind_ok decoded
      rw [pointer_suffix read]
      exact decoded
    · cases decoded

theorem allocated_fields {names : Names} {o m base node address}
    (fields : Trie.DecodedFields names.trie o m base node) :
    Trie.DecodedFields (names.allocated address).trie o m base node := by
  refine ⟨fields.peer,?_,fields.cidr,fields.width,fields.family,fields.bounded,
    fields.byteSelector,fields.bitSelector,fields.key⟩
  obtain ⟨left,right,lp,rp,shape,leftRead,leftPointer,rightRead,rightPointer⟩ := fields.children
  exact ⟨left,right,lp,rp,shape,leftRead,pointer_suffix leftPointer,rightRead,pointer_suffix rightPointer⟩

theorem decodeNode_allocate {names o m id base entry address}
    (decoded : decodeNode names o m id base=.ok entry) :
    decodeNode (names.allocated address) o m id base=.ok entry := by
  unfold decodeNode at decoded ⊢
  obtain ⟨core,read,decoded⟩ := bind_ok decoded
  obtain ⟨raw,rawRead,decoded⟩ := bind_ok decoded
  obtain ⟨slot,parentRead,decoded⟩ := bind_ok decoded
  have coreRead := (allocated_fields (Trie.decodeNode_fields read) (address:=address)).decode
  rw [coreRead]
  change (do
    let raw ← word m "node.parent" (base+AllowedipsMutationLayout.parent_bit_packed) 8
    let slot ← parent (names.allocated address) raw
    pure (id,({peer:=core.peer,bit:=core.children,cidr:=core.cidr,bitlen:=core.width,bits:=core.key,parent:=slot} : Leanux.WG.AipNode)))=_
  rw [rawRead]
  change (do
    let slot ← parent (names.allocated address) raw
    pure (id,({peer:=core.peer,bit:=core.children,cidr:=core.cidr,bitlen:=core.width,bits:=core.key,parent:=slot} : Leanux.WG.AipNode)))=_
  rw [parent_allocate parentRead]
  exact decoded

#print axioms decodeNode_allocate
#print axioms parent_root6
end Binary.Pair.Allowedips
