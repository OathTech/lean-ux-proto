import C1TrunkRootNoMem
/-! Result C1, package 2: the common exit of `add` without the relation
(`exit_tail`, after the trial's `finish_tail` and the landed
`Return.finish_checked`), and the cut's `Exits` clause for any state of
`add`'s frame whose saved words are the prologue's. -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips Binary.AllowedipsMutationImage
open Binary.TrustBase Binary.CommonBitsCoverage Binary.Instrumentation
open Binary.Statements.C1 Binary.Statements.C1.Proof Leanux Leanux.WG
local instance : Labels := Image.linkedLabels

/-- From +0x549 to `add`'s caller, given only the saved words. -/
theorem exit_tail (fetch : Int64 → Option Decoded)
    (decoder : AllowedipsMutationDecoderAgreement fetch) (tracePc : TracePcContract fetch)
    {c : Context} {s0 w : MachineData} {ra : UInt64}
    (r : Resources c s0) (readyW : CallsReady c w) (spW : w.regs.rsp = s0.regs.rsp-96)
    (loadW : ∀ off : Nat, 56 ≤ off → off+8 ≤ 104 →
      w.dmem.loadInt (s0.regs.rsp.toBitVec-104+.ofNat 64 off) 8 =
        (memory s0 8).loadInt (s0.regs.rsp.toBitVec-104+.ofNat 64 off) 8)
    (raW : w.dmem.loadInt s0.regs.rsp.toBitVec 8 = some (ra.toNat : Int)) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc = .ofBitVec ra.toBitVec ∧
      t.data.regs.rax = .ofBitVec ((w.regs.get (.low .rbx .W32)).setWidth 64) ∧
      t.data.regs.rsp = s0.regs.rsp+8 ∧
      t.data.regs.rbx = s0.regs.rbx ∧ t.data.regs.rbp = s0.regs.rbp ∧
      t.data.regs.r12 = s0.regs.r12 ∧ t.data.regs.r13 = s0.regs.r13 ∧
      t.data.regs.r14 = s0.regs.r14 ∧ t.data.regs.r15 = s0.regs.r15 ∧
      EqualOutside (fun a => Window s0 a ∨ c.writes a) w.dmem t.data.dmem)
      ⟨w,Add.entry+0x549⟩ := by
  have wordW := call_word s0 w spW
  have address (off : Nat) : w.regs.rsp.toBitVec+.ofNat 64 off =
      s0.regs.rsp.toBitVec-104+.ofNat 64 (8+off) := by
    rw [spW, UInt64.toBitVec_sub, BitVec.ofNat_add, ← BitVec.add_assoc]
    congr 1
    show s0.regs.rsp.toBitVec-96#64 = s0.regs.rsp.toBitVec-104#64+8#64
    bv_omega
  have savedWord (i : Nat) (hi : i < 6) :
      Return.saved w (88-i*8) = .ok ((words s0)[i]?.getD 0) := by
    apply saved_of_load
    rw [address, loadW _ (by omega) (by omega)]
    have read := memory_read s0 8 i (by decide) (by omega) (by omega)
    rw [slot_base s0 i (by omega)] at read
    have off : slotOffset i = 88-i*8 := by simp only [slotOffset,hi,↓reduceIte]
    rw [off] at read
    exact read
  have h0 : Return.saved w 48 = .ok s0.regs.rbx := savedWord 5 (by decide)
  have h1 : Return.saved w 56 = .ok s0.regs.rbp := savedWord 4 (by decide)
  have h2 : Return.saved w 64 = .ok s0.regs.r12 := savedWord 3 (by decide)
  have h3 : Return.saved w 72 = .ok s0.regs.r13 := savedWord 2 (by decide)
  have h4 : Return.saved w 80 = .ok s0.regs.r14 := savedWord 1 (by decide)
  have h5 : Return.saved w 88 = .ok s0.regs.r15 := savedWord 0 (by decide)
  have h6 : Return.saved w 96 = .ok ra := by
    apply saved_of_load
    rw [address]
    have top : s0.regs.rsp.toBitVec-104+.ofNat 64 (8+96) = s0.regs.rsp.toBitVec := by
      show s0.regs.rsp.toBitVec-104#64+104#64 = s0.regs.rsp.toBitVec
      bv_omega
    rw [top]
    exact raW
  have effect : Return.addEffect w = .ok ({w.regs with
      rax := .ofBitVec ((w.regs.get (.low .rbx .W32)).setWidth 64),
      rbx := s0.regs.rbx, rbp := s0.regs.rbp, r12 := s0.regs.r12, r13 := s0.regs.r13,
      r14 := s0.regs.r14, r15 := s0.regs.r15, rsp := w.regs.rsp+104},.ofBitVec ra.toBitVec) := by
    unfold Return.addEffect
    rw [h0,h1,h2,h3,h4,h5,h6]
    rfl
  have savedApart : ∀ offset ∈ [48,56,64,72,80,88,96], ∀ a,
      InRange (w.regs.rsp.toBitVec+.ofNat 64 offset) 8 a → ¬Return.Writes w c a := by
    intro offset member a inside written
    have le : offset ≤ 96 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      omega
    rw [address] at inside
    rcases (written : InRange _ 8 a ∨ c.writes a) with p | cw
    · rw [wordW] at p
      exact InRange.offset_disjoint (s0.regs.rsp.toBitVec-104) (8+offset) 8 0 8 (by omega) (by omega)
        (.inr (by omega)) a inside (by simpa using p)
    · exact r.coverageApart a (writes_bytes cw)
        (window_sub s0 (8+offset) 8 (by omega) a inside)
  have here := decoder.add _ _ (show Add.fetch (Add.entry+0x549)=some _ from rfl)
  apply eventually_trans (instructionStep fetch) _ _ _
    (Services.call fetch (Add.entry+0x549) "L_ffffffff810f31f0" .pc tracePc here c w readyW)
  rintro y ⟨pcY,stack,bx,_,_,_,_,_,_,frame⟩
  obtain ⟨regs',checked',observed'⟩ := Return.addEffect_frame stack bx frame savedApart effect
  have position : y.pc=Add.entry+0x54e := pcY
  rw [Placement.at_pc y _ position]
  apply eventually_weaken (instructionStep fetch) _ _ _ _ (Return.add_checked fetch decoder checked')
  rintro t ⟨registers,memory,pc⟩
  simp only [Return.observed,List.cons.injEq,and_true] at observed'
  obtain ⟨rax,rsp,rbx,rbp,r12,r13,r14,r15⟩ := observed'
  refine ⟨pc,registers ▸ rax,?_,registers ▸ rbx,registers ▸ rbp,registers ▸ r12,registers ▸ r13,
    registers ▸ r14,registers ▸ r15,?_⟩
  · rw [registers, rsp, spW]
    apply UInt64.toBitVec_inj.mp
    show s0.regs.rsp.toBitVec-96#64+104#64 = s0.regs.rsp.toBitVec+8#64
    bv_omega
  · rw [memory]
    intro a outside
    apply frame a
    intro h
    rcases (h : InRange _ 8 a ∨ c.writes a) with p | cw
    · rw [wordW] at p
      exact outside (.inl (window_sub s0 0 8 (by decide) a (by simpa using p)))
    · exact outside (.inr cw)

theorem low32_zext (r : Reg64s) (v : BitVec 32) (h : r.rax = .ofBitVec (v.setWidth 64)) :
    r.get (.low .rax .W32) = v := by
  simp [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.take, BitVec.drop, h]
  apply BitVec.eq_of_toNat_eq
  have lt := v.isLt
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, Nat.shiftRight_zero]
  omega

/-- The wrapper's epilogue with the stack words given in a memory `m`. -/
theorem leave_at (fetch : Int64 → Option Decoded)
    (decoder : AllowedipsMutationDecoderAgreement fetch)
    {c : Context} {s a : MachineData} {seq : BitVec 64} {v4 : Bool} {key : Nat}
    {t : MachineState} {ra : UInt64} {H : BitVec 64 → Prop} (m : Mem 64)
    (W : Nat) (wide : 200 ≤ W) (room : W ≤ s.regs.rsp.toNat) (top : s.regs.rsp.toNat + 8 ≤ 2^64)
    (atAdd : AtAdd c s seq v4 key a)
    (r13 : m.loadInt (s.regs.rsp.toBitVec - .ofNat 64 8) 8 = some (s.regs.r13.toNat : Int))
    (r12 : m.loadInt (s.regs.rsp.toBitVec - .ofNat 64 16) 8 = some (s.regs.r12.toNat : Int))
    (rbp : m.loadInt (s.regs.rsp.toBitVec - .ofNat 64 24) 8 = some (s.regs.rbp.toNat : Int))
    (rbx : m.loadInt (s.regs.rsp.toBitVec - .ofNat 64 32) 8 = some (s.regs.rbx.toNat : Int))
    (raM : m.loadInt s.regs.rsp.toBitVec 8 = some (ra.toNat : Int))
    (buffer : ∀ x, c.writes x → ¬InRange (s.regs.rsp.toBitVec - .ofNat 64 200) 208 x)
    (heapStack : ∀ x, H x → ¬InRange (s.regs.rsp.toBitVec - .ofNat 64 200) 208 x)
    (returned : Returned ⟨a,Add.entry⟩ t (site v4).toUInt64)
    (frame : EqualOutside (fun x =>
      InRange (s.regs.rsp.toBitVec - .ofNat 64 W) (W - frameSize v4 + 8) x ∨ c.writes x ∨ H x)
      m t.data.dmem) :
    Eventually (instructionStep fetch) (fun f =>
      f.pc = .ofBitVec ra.toBitVec ∧ f.data.regs.rsp = s.regs.rsp + 8 ∧
      f.data.regs.rbx = s.regs.rbx ∧ f.data.regs.rbp = s.regs.rbp ∧
      f.data.regs.r12 = s.regs.r12 ∧ f.data.regs.r13 = s.regs.r13 ∧
      f.data.regs.r14 = s.regs.r14 ∧ f.data.regs.r15 = s.regs.r15 ∧
      f.data.regs.rax = t.data.regs.rax ∧ f.data.dmem = t.data.dmem) t := by
  have stackAt := atAdd.stackAt
  cases v4
  · exact leave_core fetch decoder (a := {a with dmem := m}) false 16 rfl W wide room top stackAt
      r13 r12 rbp rbx atAdd.r14 atAdd.r15 raM buffer heapStack returned frame
  · exact leave_core fetch decoder (a := {a with dmem := m}) true 8 rfl W wide room top stackAt
      r13 r12 rbp rbx atAdd.r14 atAdd.r15 raM buffer heapStack returned frame

section
variable {fetch : Int64 → Option Decoded} {L : Statements.C1.Layout} {A : Allocator} {c : Context}
  {s : MachineState} {w : World} {v4 : Bool} {key cidr pid : Nat} {ra : UInt64}
  {names : Allowedips.Names} {stream : List HiddenRecord} {d : Device} {seq : BitVec 64}
  {a : MachineData}

/-- The cut's `Exits` clause, for any state `e` of `add`'s frame (stack
pointer below the six saved registers and the 48 bytes of locals) at which
the saved words above the locals are the prologue's and the wrapper's frame
is as it was at `add`'s entry. `FramedHolds` carries the invariant. -/
theorem exits_of_trunk (framed : FramedHolds) (premises : Premises fetch L A)
    (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a) (e : MachineState)
    (stackE : e.data.regs.rsp = a.regs.rsp - 96)
    (keptE : ∀ y, InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (frameSize v4 + 48)) (frameSize v4 + 56) y →
      e.data.dmem.get? y = (memory a 8).get? y) :
    Exits fetch L A c s ra e := by
  intro x pcX spX flightX readyX keptX
  have fs := frameSize_range v4
  have wide := window_wide A
  have r := trunk.resources
  have room := trunk.sep.room
  have room' : insertWindow + A.depth ≤ s.data.regs.rsp.toBitVec.toNat := room
  have stackAt := trunk.atAdd.stackAt
  have eBV : e.data.regs.rsp.toBitVec = s.data.regs.rsp.toBitVec - .ofNat 64 (frameSize v4 + 96) := by
    rw [stackE]
    show a.regs.rsp.toBitVec - BitVec.ofNat 64 96 = _
    rw [stackAt, sub_sub_ofNat]
  have keptX' : ∀ y, InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (frameSize v4 + 48)) (frameSize v4 + 56) y →
      x.data.dmem.get? y = e.data.dmem.get? y := by
    intro y hy
    apply keptX
    have base : e.data.regs.rsp.toBitVec + 48 =
        s.data.regs.rsp.toBitVec - .ofNat 64 (frameSize v4 + 48) := by
      rw [eBV]
      show _ + BitVec.ofNat 64 48 = _
      rw [sub_add_ofNat _ _ 48 (by omega)]
      congr 2
    have len : s.data.regs.rsp.toNat + 8 - (e.data.regs.rsp.toNat + 48) = frameSize v4 + 56 := by
      show s.data.regs.rsp.toBitVec.toNat + 8 - (e.data.regs.rsp.toBitVec.toNat + 48) = _
      rw [eBV, toNat_sub_ofNat _ _ (by omega)]
      omega
    rw [base, len]
    exact hy
  have total : EqualOutside
      (fun y => ¬InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (frameSize v4 + 48)) (frameSize v4 + 56) y)
      (memory a 8) x.data.dmem := fun y hy =>
    (keptE y (Classical.not_not.mp hy)).symm.trans (keptX' y (Classical.not_not.mp hy)).symm
  have loadSp (k n : Nat) (hk : k ≤ frameSize v4 + 48) (hn : n ≤ k + 8) :
      x.data.dmem.loadInt (s.data.regs.rsp.toBitVec - .ofNat 64 k) n =
        (memory a 8).loadInt (s.data.regs.rsp.toBitVec - .ofNat 64 k) n :=
    (total.loadInt _ n (fun i hi h =>
      h (below_sub _ k n (frameSize v4 + 48) (frameSize v4 + 56) hk (by omega) _ ⟨i,hi,rfl⟩))).symm
  have frameBase : a.regs.rsp.toBitVec - 96 = s.data.regs.rsp.toBitVec - .ofNat 64 (frameSize v4 + 96) := by
    show a.regs.rsp.toBitVec - BitVec.ofNat 64 96 = _
    rw [stackAt, sub_sub_ofNat]
  have aboveA (k n : Nat) (hk : k ≤ frameSize v4) (hn : n ≤ k + 8) :
      (memory a 8).loadInt (s.data.regs.rsp.toBitVec - .ofNat 64 k) n =
        a.dmem.loadInt (s.data.regs.rsp.toBitVec - .ofNat 64 k) n := by
    have lt := s.data.regs.rsp.toBitVec.isLt
    refine ((memory_frame a 8 (by decide)).loadInt _ n (fun i hi h => ?_)).symm
    rw [frameBase] at h
    exact below_under _ k n (frameSize v4 + 96) 96 (by omega) (by omega) (by omega) _ ⟨i,hi,rfl⟩ h
  have loadW : ∀ off : Nat, 56 ≤ off → off+8 ≤ 104 →
      x.data.dmem.loadInt (a.regs.rsp.toBitVec-104+.ofNat 64 off) 8 =
        (memory a 8).loadInt (a.regs.rsp.toBitVec-104+.ofNat 64 off) 8 := by
    intro off lo hi
    have at' : a.regs.rsp.toBitVec - 104 + .ofNat 64 off =
        s.data.regs.rsp.toBitVec - .ofNat 64 (frameSize v4 + 104 - off) := by
      show a.regs.rsp.toBitVec - BitVec.ofNat 64 104 + _ = _
      rw [stackAt, sub_sub_ofNat, sub_add_ofNat _ _ off (by omega)]
    rw [at']
    exact loadSp _ 8 (by omega) (by omega)
  have raW : x.data.dmem.loadInt a.regs.rsp.toBitVec 8 = some ((site v4).toUInt64.toNat : Int) := by
    rw [stackAt, loadSp _ 8 (by omega) (by omega), aboveA _ 8 (Nat.le_refl _) (by omega), ← stackAt]
    exact trunk.atAdd.returnWord
  have spXA : x.data.regs.rsp = a.regs.rsp - 96 := spX.trans stackE
  have wordAt (k : Nat) (hk : k ≤ 32) :
      x.data.dmem.loadInt (s.data.regs.rsp.toBitVec - .ofNat 64 k) 8 =
        a.dmem.loadInt (s.data.regs.rsp.toBitVec - .ofNat 64 k) 8 := by
    rw [loadSp k 8 (by omega) (by omega), aboveA k 8 (by omega) (by omega)]
  have zero : s.data.regs.rsp.toBitVec - .ofNat 64 0 = s.data.regs.rsp.toBitVec := by simp
  have wideStack (y : BitVec 64) (h : InRange (s.data.regs.rsp.toBitVec - .ofNat 64 200) 208 y) :
      InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (insertWindow + A.depth)) (insertWindow + A.depth + 8) y :=
    below_sub _ 200 208 (insertWindow + A.depth) (insertWindow + A.depth + 8) wide (by omega) y h
  have buffer : ∀ y, c.writes y → ¬InRange (s.data.regs.rsp.toBitVec - .ofNat 64 200) 208 y :=
    fun y h hs => trunk.sep.bytesStack y (writes_bytes h) (wideStack y hs)
  have raA : a.dmem.loadInt (s.data.regs.rsp.toBitVec - .ofNat 64 0) 8 = some (ra.toNat : Int) := by
    rw [← trunk.atAdd.frameAt.loadInt _ 8 (fun i hi h => by
      rcases h with h | h | h
      · exact below_under _ 0 8 _ _ (by omega) (by omega) (by omega) _ ⟨i,hi,rfl⟩ h
      · exact trunk.caller.seqStack _ h (below_sub _ 0 8 200 208 (by omega) (by omega) _ ⟨i,hi,rfl⟩)
      · exact buffer _ h (below_sub _ 0 8 200 208 (by omega) (by omega) _ ⟨i,hi,rfl⟩)), zero]
    exact trunk.entry.2
  have tight := window_tight trunk.atAdd (insertWindow + A.depth) wide
  rw [Placement.at_pc x _ pcX]
  apply eventually_trans (instructionStep fetch) _ _ _
    (exit_tail fetch premises.insertion premises.tracePc r readyX spXA loadW raW)
  rintro t0 ⟨pc0,rax0,rsp0,rbx0,rbp0,r12_0,r13_0,r14_0,r15_0,frame0⟩
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (leave_at fetch premises.insertion (H := fun _ => False) x.data.dmem (insertWindow + A.depth) wide
      room trunk.sep.top trunk.atAdd
      ((wordAt 8 (by omega)).trans trunk.atAdd.r13) ((wordAt 16 (by omega)).trans trunk.atAdd.r12)
      ((wordAt 24 (by omega)).trans trunk.atAdd.rbp) ((wordAt 32 (by omega)).trans trunk.atAdd.rbx)
      (by rw [← zero, wordAt 0 (by omega)]; exact raA) buffer (fun _ h => h.elim)
      ⟨pc0,rsp0,rbx0,rbp0,r12_0,r13_0,r14_0,r15_0⟩
      (fun y hy => frame0 y (fun h => hy (h.elim (fun hw => .inl (tight y hw)) (fun hc => .inr (.inl hc))))))
  rintro f ⟨pcF,spF,bxF,bpF,r12F,r13F,r14F,r15F,raxF,memF⟩
  have heapSame : ∀ y, L.Heap y → f.data.dmem.get? y = x.data.dmem.get? y := by
    intro y hy
    rw [memF]
    exact (frame0 y (fun h => h.elim (trunk.heapOutside y hy).1 (trunk.heapOutside y hy).2)).symm
  refine ⟨⟨pcF,spF,bxF,bpF,r12F,r13F,r14F,r15F⟩,low32_zext _ _ (raxF.trans rax0),?_,heapSame,
    fun w' inv => framed fetch L A premises w' x.data.dmem f.data.dmem inv (fun y hy => (heapSame y hy).symm)⟩
  rw [memF]
  intro y hy
  apply frame0 y
  intro h
  rcases h with h | h
  · exact hy (.inl (range_mono _ _ _ (by omega) y (tight y h)))
  · exact hy (.inr h)
end

#print axioms exit_tail
#print axioms leave_at
#print axioms exits_of_trunk
end C1Trunk
