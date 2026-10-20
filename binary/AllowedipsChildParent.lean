import AllowedipsParentDecode

namespace Binary.Pair.Allowedips

/-- The child tag occupies only the two low alignment bits. -/
theorem packed_child {address direction : Nat} (aligned : address%8=0) (bit : direction<2) :
    (address+(direction+1)*8) ||| direction=address+(direction+1)*8+direction := by
  have slotAligned : (address+(direction+1)*8)%4=0 := by omega
  have low := Nat.or_mod_two_pow (a:=address+(direction+1)*8) (b:=direction) (n:=2)
  have high := Nat.or_div_two_pow (a:=address+(direction+1)*8) (b:=direction) (n:=2)
  simp only [Nat.reducePow,slotAligned,Nat.mod_eq_of_lt (by omega : direction<4),Nat.zero_or] at low
  simp only [Nat.reducePow,Nat.div_eq_of_lt (by omega : direction<4),Nat.or_zero] at high
  omega

theorem parent_child {names : Names} {address direction id : Nat}
    (aligned : address%8=0) (bit : direction<2)
    (named : Trie.pointer names.trie.nodes "node.parent" address=.ok (some id)) :
    parent names ((address+(direction+1)*8) ||| direction)=.ok (.child id direction) := by
  rw [packed_child aligned bit]
  have tag : (address+(direction+1)*8+direction)%4=direction := by omega
  have slot : address+(direction+1)*8+direction-direction=address+(direction+1)*8 := by omega
  have valid : (decide (direction<2) && decide (address+(direction+1)*8≥8+8*direction))=true := by
    simp only [Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨bit,by omega⟩
  have raw : address+(direction+1)*8-8-8*direction=address := by omega
  simp only [parent,tag,slot,show (direction==2)=false from by simp; omega,
    Bool.false_eq_true,ite_false,AllowedipsLayout.bit,valid,raw,named]
  rfl

#print axioms parent_child
end Binary.Pair.Allowedips
