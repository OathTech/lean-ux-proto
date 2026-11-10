import C1Trunk.Live
/-! Result C1, package 2 (origin: trial T4, `task/binary-trials:binary-trials/t4`, copied): from `Add.entry` to the allocator's entry (the CALL at +0x42d executed). -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips Binary.AllowedipsMutationImage
open Binary.TrustBase Binary.CommonBitsCoverage Binary.Instrumentation
local instance : Labels := Image.linkedLabels

theorem low8_rbp (x : BitVec 32) (n : Nat) (value : x.toNat = n) (small : n < 256) (regs : Reg64s)
    (held : regs.rbp = .ofBitVec (x.setWidth 64)) :
    (regs.get (.low .rbp .W8)).toNat = n := by
  simp [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop,held,value]
  omega

theorem low8_r15 (x : BitVec 32) (n : Nat) (value : x.toNat = n) (small : n < 256) (regs : Reg64s)
    (held : regs.r15 = .ofBitVec (x.setWidth 64)) :
    (regs.get (.low .r15 .W8)).toNat = n := by
  simp [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop,held,value]
  omega

/-- Stage A. Every premise is a fact about the entry state. -/
theorem to_allocation (fetch : Int64 → Option Decoded)
    (decoder : AllowedipsMutationDecoderAgreement fetch)
    (tracePc : TracePcContract fetch) (cmp : AllowedipsTraceCmp1Contract fetch)
    {c : Context} {s0 : MachineData} (r : Resources c s0) (bits cidr : Nat)
    (hbits : (s0.regs.get (.low .rsi .W32)).toNat = bits)
    (hcidr : (s0.regs.get (.low .rcx .W32)).toNat = cidr)
    (bound : cidr ≤ bits) (small : bits < 256)
    (peer : s0.regs.r8.toBitVec ≠ 0)
    (rootEmpty : s0.dmem.loadInt s0.regs.rdi.toBitVec 8 = some 0)
    (rootApart : ∀ a, InRange s0.regs.rdi.toBitVec 8 a → ¬Window s0 a ∧ ¬c.writes a)
    (cache : BitVec 64) (global : s0.dmem.loadInt nodeCacheAddress 8 = some cache.toNat)
    (globalApart : ∀ a, InRange nodeCacheAddress 8 a → ¬Window s0 a ∧ ¬c.writes a) :
    Eventually (instructionStep fetch) (fun t => ∃ u, Live c s0 u ∧
      t.data.regs = {u.regs with rsi := 3520, rdi := .ofBitVec cache, rsp := u.regs.rsp-8} ∧
      t.data.dmem = Placement.callMemory u 0x432 ∧ t.pc = .ofNat 0xffffffff81196d20)
      ⟨s0,Add.entry⟩ := by
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
  have root7 : t7.data.dmem.loadInt s0.regs.rdi.toBitVec 8 = some (0#64).toNat := by
    rw [live7.outside_load _ 8 rootApart]
    exact rootEmpty
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (Add_r50_layout.agreement decoder.add) t7.data _
      (root_load t7.data s0.regs.rdi.toBitVec 0 saved7 root7))
  rintro t8 ⟨regs8,mem8,pc8⟩
  have live8 : Live c s0 t8.data := live7.quiet mem8 (by rw [regs8]) (by rw [regs8]) (by rw [regs8])
    (by rw [regs8]) (by rw [regs8]) (by rw [regs8])
  rw [ite_eq_left rfl] at pc8
  rw [Placement.at_pc t8 _ pc8]
  -- +0x41c coverage
  apply eventually_trans (instructionStep fetch) _ _ _
    (live8.call fetch tracePc (Add.entry+0x41c) (decoder.add _ _ (by rfl)))
  rintro t9 ⟨pc9,live9,_⟩
  have pc9' : t9.pc = Add.entry+0x421 := pc9
  rw [Placement.at_pc t9 _ pc9']
  -- +0x421 allocator arguments and CALL
  obtain ⟨old9,mapped9⟩ := Option.isSome_iff_exists.mp live9.ready.mapped
  have global9 : t9.data.dmem.loadInt nodeCacheAddress 8 = some cache.toNat := by
    rw [live9.outside_load _ 8 globalApart]
    exact global
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (region_eventually (Add_r421_layout.agreement decoder.add) t9.data _
      (alloc_arguments t9.data old9 cache global9 mapped9))
  rintro t10 ⟨regs10,mem10,pc10⟩
  exact ⟨t9.data,live9,regs10,mem10,pc10⟩

#print axioms to_allocation
end C1Trunk
