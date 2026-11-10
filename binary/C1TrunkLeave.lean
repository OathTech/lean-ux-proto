import C1TrunkSeq
/-! Result C1, package 2: from `add`'s return to the insertion's caller (the
wrapper's epilogue), given what `add` left of the stack. -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips Binary.AllowedipsMutationImage
open Binary.TrustBase Binary.CommonBitsCoverage Binary.Instrumentation
local instance : Labels := Image.linkedLabels

/-- The wrapper's return site for `add`. -/
def site (v4 : Bool) : Int64 := if v4 then Insert4.entry+0x42 else Insert6.entry+0x4f

theorem leave_core (fetch : Int64 → Option Decoded)
    (decoder : AllowedipsMutationDecoderAgreement fetch)
    {c : Context} {s a : MachineData} {t : MachineState} {ra : UInt64} {H : BitVec 64 → Prop}
    (v4 : Bool) (locals : Nat) (hl : locals = if v4 then 8 else 16)
    (W : Nat) (wide : 200 ≤ W) (room : W ≤ s.regs.rsp.toNat) (top : s.regs.rsp.toNat + 8 ≤ 2^64)
    (stackA : a.regs.rsp.toBitVec = s.regs.rsp.toBitVec - .ofNat 64 (40+locals))
    (r13A : a.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 8) 8 = some (s.regs.r13.toNat : Int))
    (r12A : a.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 16) 8 = some (s.regs.r12.toNat : Int))
    (rbpA : a.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 24) 8 = some (s.regs.rbp.toNat : Int))
    (rbxA : a.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 32) 8 = some (s.regs.rbx.toNat : Int))
    (r14A : a.regs.r14 = s.regs.r14) (r15A : a.regs.r15 = s.regs.r15)
    (frameA : EqualOutside (fun x =>
      InRange (s.regs.rsp.toBitVec - .ofNat 64 (40+locals)) (40+locals) x ∨
      InRange (s.regs.rdi.toBitVec+16) 8 x ∨ c.writes x) s.dmem a.dmem)
    (returnWord : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some (ra.toNat : Int))
    (buffer : ∀ x, c.writes x → ¬InRange (s.regs.rsp.toBitVec - .ofNat 64 200) 208 x)
    (seqStack : ∀ x, InRange (s.regs.rdi.toBitVec+16) 8 x →
      ¬InRange (s.regs.rsp.toBitVec - .ofNat 64 200) 208 x)
    (heapStack : ∀ x, H x → ¬InRange (s.regs.rsp.toBitVec - .ofNat 64 200) 208 x)
    (returned : Returned ⟨a,Add.entry⟩ t (site v4).toUInt64)
    (frame : EqualOutside (fun x =>
      InRange (s.regs.rsp.toBitVec - .ofNat 64 W) (W - (40+locals) + 8) x ∨ c.writes x ∨ H x)
      a.dmem t.data.dmem) :
    Eventually (instructionStep fetch) (fun f =>
      f.pc = .ofBitVec ra.toBitVec ∧ f.data.regs.rsp = s.regs.rsp + 8 ∧
      f.data.regs.rbx = s.regs.rbx ∧ f.data.regs.rbp = s.regs.rbp ∧
      f.data.regs.r12 = s.regs.r12 ∧ f.data.regs.r13 = s.regs.r13 ∧
      f.data.regs.r14 = s.regs.r14 ∧ f.data.regs.r15 = s.regs.r15 ∧
      f.data.regs.rax = t.data.regs.rax ∧ f.data.dmem = t.data.dmem) t := by
  have small : locals = 8 ∨ locals = 16 := by cases v4 <;> simp [hl]
  obtain ⟨pcT,spT,bxT,bpT,r12T,r13T,r14T,r15T⟩ := returned
  have spT' : t.data.regs.rsp = a.regs.rsp + 8 := spT
  have tsp : t.data.regs.rsp.toBitVec = s.regs.rsp.toBitVec - .ofNat 64 (32+locals) := by
    rw [spT', UInt64.toBitVec_add, stackA]
    show _ + BitVec.ofNat 64 8 = _
    rw [sub_add_ofNat _ (40+locals) 8 (by omega)]
    congr 2
    omega
  have addr (j : Nat) (hj : j ≤ 32) :
      t.data.regs.rsp.toBitVec + .ofNat 64 (locals+j) = s.regs.rsp.toBitVec - .ofNat 64 (32-j) := by
    rw [tsp, sub_add_ofNat _ (32+locals) (locals+j) (by omega)]
    congr 2
    omega
  have keep (k : Nat) (hk : k ≤ 32) :
      t.data.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 k) 8 =
        a.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 k) 8 := by
    have lt := s.regs.rsp.toNat_lt
    refine (frame.loadInt _ 8 (fun i hi h => ?_)).symm
    rcases h with h | h | h
    · exact below_under _ k 8 W (W-(40+locals)+8) (by omega) (by omega) (by omega) _ ⟨i,hi,rfl⟩ h
    · exact buffer _ h (below_sub _ k 8 200 208 (by omega) (by omega) _ ⟨i,hi,rfl⟩)
    · exact heapStack _ h (below_sub _ k 8 200 208 (by omega) (by omega) _ ⟨i,hi,rfl⟩)
  have zero : s.regs.rsp.toBitVec - .ofNat 64 0 = s.regs.rsp.toBitVec := by simp
  have top0 : a.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 0) 8 = some (ra.toNat : Int) := by
    rw [← frameA.loadInt _ 8 (fun i hi h => by
      rcases h with h | h | h
      · exact below_under _ 0 8 (40+locals) (40+locals) (by omega) (by omega) (by omega) _ ⟨i,hi,rfl⟩ h
      · exact seqStack _ h (below_sub _ 0 8 200 208 (by omega) (by omega) _ ⟨i,hi,rfl⟩)
      · exact buffer _ h (below_sub _ 0 8 200 208 (by omega) (by omega) _ ⟨i,hi,rfl⟩)), zero]
    exact returnWord
  have h0 : Return.saved t.data locals = .ok s.regs.rbx := by
    apply saved_of_load
    have e := addr 0 (by omega)
    rw [Nat.add_zero] at e
    rw [e, keep 32 (by omega)]
    exact rbxA
  have h1 : Return.saved t.data (locals+8) = .ok s.regs.rbp := by
    apply saved_of_load
    rw [addr 8 (by omega), keep 24 (by omega)]
    exact rbpA
  have h2 : Return.saved t.data (locals+16) = .ok s.regs.r12 := by
    apply saved_of_load
    rw [addr 16 (by omega), keep 16 (by omega)]
    exact r12A
  have h3 : Return.saved t.data (locals+24) = .ok s.regs.r13 := by
    apply saved_of_load
    rw [addr 24 (by omega), keep 8 (by omega)]
    exact r13A
  have h4 : Return.saved t.data (locals+32) = .ok ra := by
    apply saved_of_load
    rw [addr 32 (by omega), keep 0 (by omega)]
    exact top0
  have effect : Return.wrapperEffect v4 t.data = .ok ({t.data.regs with
      rbx := s.regs.rbx, rbp := s.regs.rbp, r12 := s.regs.r12, r13 := s.regs.r13,
      rsp := t.data.regs.rsp + .ofNat (locals+40)}, .ofBitVec ra.toBitVec) := by
    unfold Return.wrapperEffect
    rw [← hl]
    dsimp only
    rw [h0, h1, h2, h3, h4]
    rfl
  have pcT' : t.pc = (if v4 then Insert4.entry+0x42 else Insert6.entry+0x4f) := pcT
  rw [Placement.at_pc t _ pcT']
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (Return.wrapper_checked v4 fetch decoder effect)
  rintro f ⟨regsF,memF,pcF⟩
  refine ⟨pcF,?_,by rw [regsF],by rw [regsF],by rw [regsF],by rw [regsF],
    by rw [regsF]; exact r14T.trans r14A,by rw [regsF]; exact r15T.trans r15A,by rw [regsF],memF⟩
  rw [regsF]
  apply UInt64.toBitVec_inj.mp
  show t.data.regs.rsp.toBitVec + BitVec.ofNat 64 (locals+40) = s.regs.rsp.toBitVec + 8
  rw [tsp]
  rcases small with h | h <;> subst h
  · show s.regs.rsp.toBitVec - 40#64 + 48#64 = s.regs.rsp.toBitVec + 8#64
    bv_omega
  · show s.regs.rsp.toBitVec - 48#64 + 56#64 = s.regs.rsp.toBitVec + 8#64
    bv_omega

#print axioms leave_core
end C1Trunk
