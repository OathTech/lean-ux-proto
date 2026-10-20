import StackFrame

namespace Binary.Pair.Stack

def slot (sp : BitVec 64) (i : Nat) : BitVec 64 := sp-.ofNat 64 (8*i)

theorem window (sp : BitVec 64) (words i : Nat) (bound : i≤words) :
    slot sp i=slot sp words+.ofNat 64 (8*(words-i)) := by
  have number : 8*words=8*i+8*(words-i) := by omega
  simp only [slot]
  rw [number,BitVec.ofNat_add,←BitVec.sub_sub,BitVec.sub_add_cancel]

theorem separate (sp : BitVec 64) (words i j : Nat) (size : words<2^60)
    (left : i≤words) (right : j≤words) (different : i≠j) :
    ∀ a, InRange (slot sp i) 8 a → ¬InRange (slot sp j) 8 a := by
  rw [window sp words i left,window sp words j right]
  apply InRange.offset_disjoint <;> omega

theorem inside (sp : BitVec 64) (words i : Nat) (bound : i≤words)
    (a : BitVec 64) (atSlot : InRange (slot sp i) 8 a) :
    InRange (slot sp words) (8*words+8) a := by
  obtain ⟨byte,hb,eq⟩ := atSlot
  exact ⟨8*(words-i)+byte,by omega,by
    simpa only [window sp words i bound,BitVec.ofNat_add,BitVec.add_assoc] using eq⟩

theorem scratch (sp : BitVec 64) (words i : Nat) (lower : 1≤i) (bound : i≤words)
    (a : BitVec 64) (atSlot : InRange (slot sp i) 8 a) :
    InRange (slot sp words) (8*words) a := by
  obtain ⟨byte,hb,eq⟩ := atSlot
  exact ⟨8*(words-i)+byte,by omega,by
    simpa only [window sp words i bound,BitVec.ofNat_add,BitVec.add_assoc] using eq⟩

def save (m : DataMem) (sp : BitVec 64) (values : List UInt64) : Nat → DataMem
  | 0 => m
  | n+1 => (save m sp values n).storeInt (slot sp (n+1)) 8 (values[n]?.getD 0).toBitVec.toInt

theorem mapped (m : DataMem) (sp : BitVec 64) (values : List UInt64) (n : Nat)
    (base : BitVec 64) (width : Nat) (read : (m.loadInt base width).isSome=true) :
    ((save m sp values n).loadInt base width).isSome=true := by
  induction n with
  | zero => exact read
  | succ n ih => exact storeInt_defined _ _ _ _ _ _ ih

theorem read (m : DataMem) (sp : BitVec 64) (values : List UInt64) (n i : Nat)
    (bound : n<2^60) (saved : i<n) :
    (save m sp values n).loadInt (slot sp (i+1)) 8=some (values[i]?.getD 0).toNat := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases last : i=n
    · subst i
      exact load64_store _ _ _
    · have before := ih (by omega) (by omega)
      have frame := storeInt_frame (save m sp values n) (slot sp (n+1)) 8 (values[n]?.getD 0).toBitVec.toInt
      have same := frame.loadInt (slot sp (i+1)) 8 (by
        intro byte hb
        exact separate sp (n+1) (i+1) (n+1) bound (by omega) (by omega) (by omega) _ ⟨byte,hb,rfl⟩)
      exact same.symm.trans before

theorem frame (m : DataMem) (sp : BitVec 64) (values : List UInt64) (words n : Nat)
    (bound : n≤words) : EqualOutside (InRange (slot sp words) (8*words)) m (save m sp values n) := by
  induction n with
  | zero => intro a outside; rfl
  | succ n ih =>
    intro a outside
    exact (ih (by omega) a outside).trans
      (storeInt_frame _ _ _ _ a (fun atSlot => outside (scratch sp words (n+1) (by omega) (by omega) a atSlot)))

theorem return_read (m : DataMem) (sp : BitVec 64) (values : List UInt64) (n : Nat)
    (bound : n<2^60) : (save m sp values n).loadInt sp 8=m.loadInt sp 8 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have frame := storeInt_frame (save m sp values n) (slot sp (n+1)) 8 (values[n]?.getD 0).toBitVec.toInt
    have same := frame.loadInt sp 8 (by
      intro byte hb
      have atSlot : InRange (slot sp 0) 8 (sp+.ofNat 64 byte) := by simpa [slot] using (show InRange sp 8 (sp+.ofNat 64 byte) from ⟨byte,hb,rfl⟩)
      exact separate sp (n+1) 0 (n+1) bound (by omega) (by omega) (by omega) _ atSlot)
    exact same.symm.trans (ih (by omega))

#print axioms read
#print axioms frame
#print axioms return_read
end Binary.Pair.Stack
