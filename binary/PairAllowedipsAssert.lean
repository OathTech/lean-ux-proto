import PairAllowedipsDecode

namespace Binary.Pair.Allowedips
open Leanux Leanux.WG

local instance : LawfulBEq Slot where
  eq_of_beq := by
    intro a b equal
    cases a <;> cases b <;> simp_all [BEq.beq,instBEqSlot.beq]
  rfl := by intro a; cases a <;> simp [BEq.beq,instBEqSlot.beq]

local instance : LawfulBEq AipNode where
  eq_of_beq := by
    rintro ⟨p,b,c,w,k,s⟩ ⟨p',b',c',w',k',s'⟩ equal
    change (p==p' && (b==b' && (c==c' && (w==w' && (k==k' && s==s')))))=true at equal
    have parts : (((((p=p' ∧ b=b') ∧ c=c') ∧ w=w') ∧ k=k') ∧ s=s') := by
      simpa only [Bool.and_eq_true,beq_iff_eq,and_assoc] using equal
    rcases parts with ⟨⟨⟨⟨⟨rfl,rfl⟩,rfl⟩,rfl⟩,rfl⟩,rfl⟩
    rfl
  rfl := by
    rintro ⟨p,b,c,w,k,s⟩
    change (p==p && (b==b && (c==c && (w==w && (k==k && s==s)))))=true
    simp

local instance : LawfulBEq AllowedIps where
  eq_of_beq := by
    rintro ⟨r4,r6,seq⟩ ⟨r4',r6',seq'⟩ equal
    change (r4==r4' && (r6==r6' && seq==seq'))=true at equal
    have parts : (r4=r4' ∧ r6=r6') ∧ seq=seq' := by
      simpa only [Bool.and_eq_true,beq_iff_eq,and_assoc] using equal
    rcases parts with ⟨⟨rfl,rfl⟩,rfl⟩
    rfl
  rfl := by
    rintro ⟨r4,r6,seq⟩
    change (r4==r4 && (r6==r6 && seq==seq))=true
    simp

theorem assertAt_ok {names o m w} (ok : assertAt names o m w = .ok ()) :
    ∃ d, w.wg.dev=some d ∧ Corresponds names o m d ∧ heap names (target d) m=.ok () := by
  unfold assertAt at ok
  cases device : w.wg.dev with
  | none => rw [device] at ok; cases ok
  | some d =>
    rw [device] at ok
    obtain ⟨actual,decoded,ok⟩ := bind_ok ok
    obtain ⟨table,ok⟩ := check_ok _ _ _ _ ok
    obtain ⟨nodes,ok⟩ := check_ok _ _ _ _ ok
    obtain ⟨peers,ok⟩ := check_ok _ _ _ _ ok
    obtain ⟨counter,ok⟩ := check_ok _ _ _ _ ok
    have equal : actual=target d := by
      cases actual
      have ht := eq_of_beq table
      have hn := eq_of_beq nodes
      have hp := eq_of_beq peers
      have hc := eq_of_beq counter
      cases ht; cases hn; cases hp; cases hc
      rfl
    subst actual
    exact ⟨d,rfl,mapError_ok decoded,ok⟩

theorem assertAt_of_related {names o m w d}
    (device : w.wg.dev=some d) (related : Corresponds names o m d)
    (shape : heap names (target d) m=.ok ()) : assertAt names o m w=.ok () := by
  unfold assertAt
  rw [device,related]
  dsimp only [Except.mapError,Bind.bind,Except.bind]
  simpa only [beq_self_eq_true,↓reduceIte] using shape

#print axioms assertAt_ok
end Binary.Pair.Allowedips
