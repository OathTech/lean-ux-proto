import C1TrunkHeld
import C1TrunkWalkRegions
/-! Result C1, package 2: `add` on a nonempty root, from its entry to the
placement loop's header at +0xf7 (the prologue and guards as in
`to_allocation`, then the callback at +0x61 and the regions r66 and r83).
`AtHeader` is what the landed loop's header needs of the machine, stated
against `add`'s entry state. -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips Binary.AllowedipsMutationImage
open Binary.TrustBase Binary.CommonBitsCoverage Binary.Instrumentation
local instance : Labels := Image.linkedLabels

theorem low32_rbp (x : BitVec 32) (regs : Reg64s) (held : regs.rbp = .ofBitVec (x.setWidth 64)) :
    regs.get (.low .rbp .W32) = x := by
  simp [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop,held]
  apply BitVec.eq_of_toNat_eq
  have lt := x.isLt
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, Nat.shiftRight_zero]
  omega

theorem zext32_toNat (x : BitVec 32) : (UInt64.ofBitVec (x.setWidth 64)).toNat = x.toNat := by
  show (x.setWidth 64).toNat = x.toNat
  have lt := x.isLt
  simp only [BitVec.toNat_setWidth]
  omega

theorem zext8_toNat (x : BitVec 8) : (UInt64.ofBitVec (x.setWidth 64)).toNat = x.toNat := by
  show (x.setWidth 64).toNat = x.toNat
  have lt := x.isLt
  simp only [BitVec.toNat_setWidth]
  omega

theorem sp_frame (a : MachineData) (sp : UInt64) (stack : sp = a.regs.rsp-96) (k : Nat) :
    sp.toBitVec+.ofNat 64 k = a.regs.rsp.toBitVec-104+.ofNat 64 (8+k) := by
  rw [stack, UInt64.toBitVec_sub, BitVec.ofNat_add, ← BitVec.add_assoc]
  congr 1
  show a.regs.rsp.toBitVec-96#64 = a.regs.rsp.toBitVec-104#64+8#64
  bv_omega

theorem locals_parent (a : MachineData) (sp : UInt64) (stack : sp = a.regs.rsp-96) (x : BitVec 64)
    (h : InRange sp.toBitVec 8 x) : Locals a x := by
  obtain ⟨i,hi,eq⟩ := h
  refine .inl ⟨48+i,by omega,?_⟩
  rw [eq, stack, UInt64.toBitVec_sub, BitVec.ofNat_add, ← BitVec.add_assoc]
  congr 1
  show a.regs.rsp.toBitVec-96#64 = a.regs.rsp.toBitVec-144#64+48#64
  bv_omega

theorem locals_width (a : MachineData) (sp : UInt64) (stack : sp = a.regs.rsp-96) (x : BitVec 64)
    (h : InRange (sp.toBitVec+0x24) 4 x) : Locals a x :=
  .inr (.inr (by rw [← sp_frame a sp stack 36]; exact h))

theorem locals_owner (a : MachineData) (sp : UInt64) (stack : sp = a.regs.rsp-96) (x : BitVec 64)
    (h : InRange (sp.toBitVec+0x18) 8 x) : Locals a x :=
  .inr (.inl (by rw [← sp_frame a sp stack 24]; exact h))

/-- The machine at the placement loop's header on a nonempty root. -/
structure AtHeader (c : Context) (a : MachineData) (root : BitVec 64) (bits : Nat) (h : MachineState) :
    Prop where
  pc : h.pc = Add.entry+0xf7
  held : Held c a h.data
  rbx : h.data.regs.rbx = .ofBitVec root
  rbp : h.data.regs.rbp.toNat = bits
  r14 : h.data.regs.r14 = a.regs.r8
  r15 : h.data.regs.r15.toNat = bits
  parent : h.data.dmem.loadInt h.data.regs.rsp.toBitVec 8 = some ((0 : Nat) : Int)
  width : h.data.dmem.loadInt (h.data.regs.rsp.toBitVec+0x24) 4 = some (bits : Int)
  owner : h.data.dmem.loadInt (h.data.regs.rsp.toBitVec+0x18) 8 = some (a.regs.r8.toNat : Int)

/-- `add`'s entry to the loop's header. Every premise is a fact about the entry state. -/
theorem to_header (fetch : Int64 → Option Decoded)
    (decoder : AllowedipsMutationDecoderAgreement fetch)
    (tracePc : TracePcContract fetch) (cmp : AllowedipsTraceCmp1Contract fetch)
    {c : Context} {s0 : MachineData} (r : Resources c s0) (bits cidr : Nat)
    (hbits : (s0.regs.get (.low .rsi .W32)).toNat = bits)
    (hcidr : (s0.regs.get (.low .rcx .W32)).toNat = cidr)
    (bound : cidr ≤ bits) (small : bits < 256)
    (peer : s0.regs.r8.toBitVec ≠ 0)
    (root : BitVec 64) (rootNonzero : root ≠ 0)
    (rootWord : s0.dmem.loadInt s0.regs.rdi.toBitVec 8 = some root.toNat)
    (rootApart : ∀ a, InRange s0.regs.rdi.toBitVec 8 a → ¬Wide s0 a ∧ ¬c.writes a)
    (localsMapped : ∀ off n : Nat, 8 ≤ off → off+n ≤ 56 →
      (s0.dmem.loadInt (s0.regs.rsp.toBitVec-104+.ofNat 64 off) n).isSome = true)
    (scratch : ∀ x, c.bytes x → ¬Wide s0 x) :
    Eventually (instructionStep fetch) (AtHeader c s0 root bits) ⟨s0,Add.entry⟩ := by
  -- prologue
  have start : (⟨s0,Add.entry⟩ : MachineState) = ⟨s0,Add.entry+.ofNat 0⟩ := rfl
  rw [start]
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (prologue_layout.agreement decoder.add) s0 _ (prologue s0 r.slots))
  rintro t1 ⟨regs1,mem1,pc1⟩
  have live1 := Live.initial r t1.data regs1 mem1
  rw [Placement.at_pc t1 _ pc1]
  -- +0x25 coverage
  apply eventually_trans (instructionStep fetch) _ _ _
    (live1.call fetch tracePc (Add.entry+0x25) (decoder.add _ _ (by rfl)))
  rintro t2 ⟨pc2,live2,_⟩
  have pc2' : t2.pc = Add.entry+0x2a := pc2
  rw [Placement.at_pc t2 _ pc2']
  -- +0x2a comparison callback
  obtain ⟨old2,mapped2⟩ := Option.isSome_iff_exists.mp live2.ready.mapped
  have called := region_callback fetch (.ofNat 0xffffffff810f4040) (Add.entry+0x34) .cmp1 cmp c
    ⟨t2.data,Add.entry+0x2a⟩ t2.data
    {t2.data.regs with
      rsi := .ofBitVec ((t2.data.regs.get (.low .rbp .W32)).setWidth 64),
      rdi := .ofBitVec ((t2.data.regs.get (.low .r15 .W32)).setWidth 64)}
    live2.ready
    (region_eventually (Add_r2a_layout.agreement decoder.add) t2.data _ (cmp_arguments t2.data old2 mapped2))
  apply eventually_trans (instructionStep fetch) _ _ _ called
  rintro t3 ⟨pc3,sp3,_,bp3,r12_3,r13_3,r14_3,r15_3,ready3,frame3⟩
  have live3 := live2.next ready3 sp3 bp3 r12_3 r13_3 r14_3 r15_3 frame3
  rw [Placement.at_pc t3 _ pc3]
  -- +0x34 cidr guard
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (Add_r34_layout.agreement decoder.add) t3.data _ (cidr_guard t3.data))
  rintro t4 ⟨regs4,mem4,pc4⟩
  have live4 : Live c s0 t4.data := live3.quiet mem4 (by rw [regs4]) (by rw [regs4]) (by rw [regs4])
    (by rw [regs4]) (by rw [regs4]) (by rw [regs4])
  have bitsByte : (t3.data.regs.get (.low .rbp .W8)).toNat = bits :=
    low8_rbp _ bits hbits small _ live3.bits
  have cidrByte : (t3.data.regs.get (.low .r15 .W8)).toNat = cidr :=
    low8_r15 _ cidr hcidr (by omega) _ live3.cidr15
  rw [bitsByte,cidrByte,ite_eq_right (by omega)] at pc4
  rw [Placement.at_pc t4 _ pc4]
  -- +0x3d coverage
  apply eventually_trans (instructionStep fetch) _ _ _
    (live4.call fetch tracePc (Add.entry+0x3d) (decoder.add _ _ (by rfl)))
  rintro t5 ⟨pc5,live5,_⟩
  have pc5' : t5.pc = Add.entry+0x42 := pc5
  rw [Placement.at_pc t5 _ pc5']
  -- +0x42 peer guard
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (Add_r42_layout.agreement decoder.add) t5.data _ (peer_guard t5.data))
  rintro t6 ⟨regs6,mem6,pc6⟩
  have live6 : Live c s0 t6.data := live5.quiet mem6 (by rw [regs6]) (by rw [regs6]) (by rw [regs6])
    (by rw [regs6]) (by rw [regs6]) (by rw [regs6])
  rw [live5.peer,ite_eq_right peer] at pc6
  rw [Placement.at_pc t6 _ pc6]
  -- +0x4b coverage
  apply eventually_trans (instructionStep fetch) _ _ _
    (live6.call fetch tracePc (Add.entry+0x4b) (decoder.add _ _ (by rfl)))
  rintro t7 ⟨pc7,live7,_⟩
  have pc7' : t7.pc = Add.entry+0x50 := pc7
  rw [Placement.at_pc t7 _ pc7']
  -- +0x50 root load
  have savedAddress : t7.data.regs.rsp.toBitVec+8 = s0.regs.rsp.toBitVec-104+.ofNat 64 16 := by
    rw [live7.stack, UInt64.toBitVec_sub]
    show s0.regs.rsp.toBitVec-96#64+8#64 = s0.regs.rsp.toBitVec-104#64+16#64
    bv_omega
  have saved7 : t7.data.dmem.loadInt (t7.data.regs.rsp.toBitVec+8) 8 = some s0.regs.rdi.toBitVec.toNat := by
    rw [savedAddress, live7.window_load r 16 8 (by decide) (by decide)]
    have read := memory_read s0 8 6 (by decide) (by decide) (by decide)
    rw [slot_base s0 6 (by decide)] at read
    exact read
  have rootWindow : ∀ a, InRange s0.regs.rdi.toBitVec 8 a → ¬Window s0 a ∧ ¬c.writes a :=
    fun a h => ⟨fun w => (rootApart a h).1 (wide_of_window s0 a w),(rootApart a h).2⟩
  have root7 : t7.data.dmem.loadInt s0.regs.rdi.toBitVec 8 = some root.toNat := by
    rw [live7.outside_load _ 8 rootWindow]
    exact rootWord
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (Add_r50_layout.agreement decoder.add) t7.data _
      (root_load t7.data s0.regs.rdi.toBitVec root saved7 root7))
  rintro t8 ⟨regs8,mem8,pc8⟩
  have live8 : Live c s0 t8.data := live7.quiet mem8 (by rw [regs8]) (by rw [regs8]) (by rw [regs8])
    (by rw [regs8]) (by rw [regs8]) (by rw [regs8])
  rw [ite_eq_right rootNonzero] at pc8
  rw [Placement.at_pc t8 _ pc8]
  -- +0x61 coverage
  apply eventually_trans (instructionStep fetch) _ _ _
    (live8.call fetch tracePc (Add.entry+0x61) (decoder.add _ _ (by rfl)))
  rintro t9 ⟨pc9,live9,_⟩
  have pc9' : t9.pc = Add.entry+0x66 := pc9
  rw [Placement.at_pc t9 _ pc9']
  -- +0x66 the walk's setup
  have held9 := Held.ofLive live9
  have frameMapped (off n : Nat) (lo : 8 ≤ off) (hi : off+n ≤ 56) :
      (t9.data.dmem.loadInt (s0.regs.rsp.toBitVec-104+.ofNat 64 off) n).isSome = true := by
    rw [live9.window_load r off n lo (by omega)]
    exact memory_mapped s0 8 n _ (localsMapped off n lo hi)
  have sp9 (k : Nat) := sp_frame s0 t9.data.regs.rsp live9.stack k
  have sp9zero : t9.data.regs.rsp.toBitVec = s0.regs.rsp.toBitVec-104+.ofNat 64 8 := by
    have h := sp9 0
    simpa using h
  have saved9 : t9.data.dmem.loadInt (t9.data.regs.rsp.toBitVec+8) 8 = some s0.regs.rdi.toBitVec.toNat := by
    rw [show t9.data.regs.rsp.toBitVec+8 = s0.regs.rsp.toBitVec-104+.ofNat 64 16 from sp9 8,
      live9.window_load r 16 8 (by decide) (by decide)]
    have read := memory_read s0 8 6 (by decide) (by decide) (by decide)
    rw [slot_base s0 6 (by decide)] at read
    exact read
  obtain ⟨old9,mapped9⟩ := Option.isSome_iff_exists.mp (sp9zero ▸ frameMapped 8 8 (by decide) (by decide))
  have root9 : (t9.data.dmem.storeInt t9.data.regs.rsp.toBitVec 8 0).loadInt s0.regs.rdi.toBitVec 8 =
      some root.toNat := by
    rw [load_store_apart _ _ _ _ _ _ (fun x hx hs =>
      (rootApart x hx).1 (wide_of_locals s0 x (locals_parent s0 _ live9.stack x hs))),
      live9.outside_load _ 8 rootWindow]
    exact rootWord
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (Add_r66_layout.agreement decoder.add) t9.data _
      (walk_setup t9.data s0.regs.rdi.toBitVec root old9 saved9 mapped9 root9))
  rintro t10 ⟨regs10,mem10,pc10⟩
  have held10 : Held c s0 t10.data := held9.store t9.data.regs.rsp.toBitVec 8 0
    (fun x hx => locals_parent s0 _ live9.stack x hx) mem10 (by rw [regs10]) (by rw [regs10])
    (by rw [regs10]) scratch
  rw [ite_eq_right rootNonzero] at pc10
  rw [Placement.at_pc t10 _ pc10]
  -- +0x83 the saved width and owner
  have sp10 : t10.data.regs.rsp = t9.data.regs.rsp := by rw [regs10]
  have bp10 : t10.data.regs.rbp = .ofBitVec ((s0.regs.get (.low .rsi .W32)).setWidth 64) := by
    rw [regs10]; exact live9.bits
  have widthValue : t10.data.regs.get (.low .rbp .W32) = s0.regs.get (.low .rsi .W32) :=
    low32_rbp _ _ bp10
  have widthMapped : (t10.data.dmem.loadInt (t10.data.regs.rsp.toBitVec+0x24) 4).isSome = true := by
    rw [mem10, sp10]
    apply storeInt_defined
    rw [show t9.data.regs.rsp.toBitVec+0x24 = s0.regs.rsp.toBitVec-104+.ofNat 64 44 from sp9 36]
    exact frameMapped 44 4 (by decide) (by decide)
  have ownerMapped : (t10.data.dmem.loadInt (t10.data.regs.rsp.toBitVec+0x18) 8).isSome = true := by
    rw [mem10, sp10]
    apply storeInt_defined
    rw [show t9.data.regs.rsp.toBitVec+0x18 = s0.regs.rsp.toBitVec-104+.ofNat 64 32 from sp9 24]
    exact frameMapped 32 8 (by decide) (by decide)
  obtain ⟨oldWidth,mappedWidth⟩ := Option.isSome_iff_exists.mp widthMapped
  obtain ⟨oldOwner,mappedOwner⟩ := Option.isSome_iff_exists.mp
    (storeInt_defined t10.data.dmem _ (t10.data.regs.rsp.toBitVec+0x24) 8 4
      (t10.data.regs.get (.low .rbp .W32)).toInt ownerMapped)
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (region_eventually (Add_r83_layout.agreement decoder.add) t10.data _
      (walk_locals t10.data oldWidth oldOwner mappedWidth mappedOwner))
  rintro t11 ⟨regs11,mem11,pc11⟩
  have stack10 : t10.data.regs.rsp = s0.regs.rsp-96 := held10.stack
  let mid : MachineData := {t10.data with
    dmem := t10.data.dmem.storeInt (t10.data.regs.rsp.toBitVec+0x24) 4 (t10.data.regs.get (.low .rbp .W32)).toInt}
  have heldMid : Held c s0 mid := held10.store (t10.data.regs.rsp.toBitVec+0x24) 4 _
    (fun x hx => locals_width s0 _ stack10 x hx) rfl rfl rfl rfl scratch
  have held11 : Held c s0 t11.data := heldMid.store (t10.data.regs.rsp.toBitVec+0x18) 8 _
    (fun x hx => locals_owner s0 _ stack10 x hx) mem11 (by rw [regs11]) (by rw [regs11])
    (by rw [regs11]) scratch
  have sp11 : t11.data.regs.rsp = t10.data.regs.rsp := by rw [regs11]
  have apartOf (i ni j nj : Nat) (h : i+ni ≤ j ∨ j+nj ≤ i) (bi : i+ni ≤ 64) (bj : j+nj ≤ 64) :
      ∀ x, InRange (t10.data.regs.rsp.toBitVec+.ofNat 64 i) ni x →
        ¬InRange (t10.data.regs.rsp.toBitVec+.ofNat 64 j) nj x :=
    fun x hx => InRange.offset_disjoint t10.data.regs.rsp.toBitVec i ni j nj (by omega) (by omega) h x hx
  have atZero (x : BitVec 64) (hx : InRange t10.data.regs.rsp.toBitVec 8 x) :
      InRange (t10.data.regs.rsp.toBitVec+.ofNat 64 0) 8 x := by simpa using hx
  have parentOwner : ∀ x, InRange t10.data.regs.rsp.toBitVec 8 x →
      ¬InRange (t10.data.regs.rsp.toBitVec+0x18) 8 x :=
    fun x hx => apartOf 0 8 24 8 (by omega) (by omega) (by omega) x (atZero x hx)
  have parentWidth : ∀ x, InRange t10.data.regs.rsp.toBitVec 8 x →
      ¬InRange (t10.data.regs.rsp.toBitVec+0x24) 4 x :=
    fun x hx => apartOf 0 8 36 4 (by omega) (by omega) (by omega) x (atZero x hx)
  have widthOwner : ∀ x, InRange (t10.data.regs.rsp.toBitVec+0x24) 4 x →
      ¬InRange (t10.data.regs.rsp.toBitVec+0x18) 8 x :=
    apartOf 36 4 24 8 (by omega) (by omega) (by omega)
  refine ⟨pc11,held11,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [regs11, regs10]
  · rw [regs11, bp10, zext32_toNat]
    exact hbits
  · rw [regs11, regs10]
    exact live9.peer
  · rw [regs11, regs10]
    show (UInt64.ofBitVec ((t9.data.regs.get (.low .rbp .W8)).setWidth 64)).toNat = bits
    rw [zext8_toNat]
    exact low8_rbp _ bits hbits small _ live9.bits
  · rw [mem11, sp11, load_store_apart _ _ _ _ _ _ parentOwner,
      load_store_apart _ _ _ _ _ _ parentWidth, mem10, sp10]
    exact load64_store _ _ 0
  · rw [mem11, sp11, load_store_apart _ _ _ _ _ _ widthOwner, load32_store, widthValue, hbits]
  · rw [mem11, sp11, load64_store, regs10]
    show some ((t9.data.regs.r14.toNat : Nat) : Int) = _
    rw [live9.peer]

#print axioms to_header
end C1Trunk
