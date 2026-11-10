import C1TrunkCaller
import AllowedipsCounterRegion
/-! Result C1, package 2: from a wrapper's entry to `add`'s entry (prologue,
coverage callback, sequence increment, address copy and byte swap, CALL). -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips Binary.AllowedipsMutationImage
open Binary.TrustBase Binary.CommonBitsCoverage Binary.Instrumentation
local instance : Labels := Image.linkedLabels

/-- The machine at `add`'s entry, against the wrapper's caller `s`. `seq` is
the sequence word before the call and `key` the address in host order. -/
structure AtAdd (c : Context) (s : MachineData) (seq : BitVec 64) (v4 : Bool) (key : Nat)
    (a : MachineData) : Prop where
  stack : a.regs.rsp = s.regs.rsp - (if v4 then 48 else 56)
  slot : a.regs.rdi = if v4 then s.regs.rdi else s.regs.rdi+8
  bits : (a.regs.get (.low .rsi .W32)).toNat = if v4 then 32 else 128
  query : a.regs.rdx = s.regs.rsp - (if v4 then 36 else 48)
  cidr : (a.regs.get (.low .rcx .W32)).toNat = s.regs.rdx.toNat % 256
  peer : a.regs.r8 = s.regs.rcx
  returnWord : a.dmem.loadInt a.regs.rsp.toBitVec 8 =
    some ((if v4 then Insert4.entry+.ofNat 0x42 else Insert6.entry+.ofNat 0x4f).toBitVec.toNat : Int)
  r13 : a.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 8) 8 = some (s.regs.r13.toNat : Int)
  r12 : a.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 16) 8 = some (s.regs.r12.toNat : Int)
  rbp : a.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 24) 8 = some (s.regs.rbp.toNat : Int)
  rbx : a.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 32) 8 = some (s.regs.rbx.toNat : Int)
  keyWord : if v4 then a.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 36) 4 = some (key : Int)
    else a.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 48) 8 = some ((key / 2^64 : Nat) : Int) ∧
      a.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 40) 8 = some ((key % 2^64 : Nat) : Int)
  seqWord : a.dmem.loadInt (s.regs.rdi.toBitVec+16) 8 = some ((1+seq).toNat : Int)
  frame : EqualOutside (fun x =>
    InRange (s.regs.rsp.toBitVec - .ofNat 64 (if v4 then 48 else 56)) (if v4 then 48 else 56) x ∨
    InRange (s.regs.rdi.toBitVec+16) 8 x ∨ c.writes x) s.dmem a.dmem
  coverage : c.At a.dmem

theorem aligned_sub (x : UInt64) (k : Nat) (hk : k % 8 = 0) (small : k ≤ 200)
    (aligned : x.toNat % 8 = 0) (room : 200 ≤ x.toNat) : (x - .ofNat k).toNat % 8 = 0 := by
  have lt := x.toNat_lt
  have bound := room
  rw [UInt64.toNat_sub, UInt64.toNat_ofNat']
  have : k % 2^64 = k := Nat.mod_eq_of_lt (by omega)
  omega

theorem cidr_reg (s t u : Reg64s)
    (bp : t.rbp = .ofBitVec ((s.get (.low .rdx .W32)).setWidth 64))
    (cx : u.rcx = .ofBitVec ((t.get (.low .rbp .W8)).setWidth 64)) :
    (u.get (.low .rcx .W32)).toNat = s.rdx.toNat % 256 := by
  simp [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop,bp,cx]
  omega

/-- The v4 wrapper, entry to `add`'s entry. -/
theorem enter4 (fetch : Int64 → Option Decoded)
    (decoder : AllowedipsMutationDecoderAgreement fetch) (tracePc : TracePcContract fetch)
    {c : Context} {s : MachineData} {seq : BitVec 64} (caller : Caller c s seq)
    (network : BitVec 32)
    (word : s.dmem.loadInt s.regs.rsi.toBitVec 4 = some (network.toNat : Int))
    (keyStack : ∀ a, InRange s.regs.rsi.toBitVec 4 a →
      ¬InRange (s.regs.rsp.toBitVec - .ofNat 64 200) 200 a)
    (keyBuffer : ∀ a, InRange s.regs.rsi.toBitVec 4 a → ¬c.writes a)
    (keySeq : ∀ a, InRange s.regs.rsi.toBitVec 4 a → ¬InRange (s.regs.rdi.toBitVec+16) 8 a) :
    Eventually (instructionStep fetch) (fun t => t.pc = Add.entry ∧
      AtAdd c s seq true (Allowedips.swap32 network).toNat t.data) ⟨s,Insert4.entry⟩ := by
  have sp := s.regs.rsp.toBitVec
  have start : (⟨s,Insert4.entry⟩ : MachineState) = ⟨s,Insert4.entry+.ofNat 0⟩ := rfl
  rw [start]
  -- prologue
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (prologue4_layout.agreement decoder.insert4) s _
      (prologue4 s _ (caller.below.load 8 8 (by omega) (by omega))
        (caller.below.load 16 8 (by omega) (by omega)) (caller.below.load 24 8 (by omega) (by omega))
        (caller.below.load 32 8 (by omega) (by omega))))
  rintro t1 ⟨regs1,mem1,pc1⟩
  have rsp1 : t1.data.regs.rsp = s.regs.rsp - 40 := by rw [regs1]
  have word1 : t1.data.regs.rsp.toBitVec - 8 = s.regs.rsp.toBitVec - .ofNat 64 48 := by
    rw [rsp1, UInt64.toBitVec_sub]
    show s.regs.rsp.toBitVec - 40#64 - 8#64 = s.regs.rsp.toBitVec - 48#64
    bv_omega
  have ready1 : CallsReady c t1.data := caller.ready 48 (by omega) (by omega) t1.data word1
    (by rw [rsp1]; exact aligned_sub _ 40 (by omega) (by omega) caller.aligned caller.room) mem1
  have pc1' : t1.pc = Insert4.entry+0x15 := pc1
  rw [Placement.at_pc t1 _ pc1']
  -- coverage callback
  apply eventually_trans (instructionStep fetch) _ _ _
    (Services.call fetch (Insert4.entry+0x15) "L_ffffffff810f31f0" .pc tracePc
      (decoder.insert4 _ _ (by rfl)) c t1.data ready1)
  rintro t2 ⟨pc2,sp2,bx2,bp2,r12_2,r13_2,_,_,ready2,frame2⟩
  rw [word1, mem1] at frame2
  have pre : Frames c s seq 48 t2.data.dmem
      (t2.data.dmem.storeInt (s.regs.rdi.toBitVec+16) 8 (1+seq).toInt) :=
    ⟨frame2,ready2.state,fun _ _ => rfl⟩
  have rbx2 : t2.data.regs.rbx = s.regs.rdi := bx2.trans (by rw [regs1])
  have rbp2 : t2.data.regs.rbp = .ofBitVec ((s.regs.get (.low .rdx .W32)).setWidth 64) :=
    bp2.trans (by rw [regs1])
  have r12two : t2.data.regs.r12 = s.regs.rcx := r12_2.trans (by rw [regs1])
  have r13two : t2.data.regs.r13 = s.regs.rsi := r13_2.trans (by rw [regs1])
  have rsp2 : t2.data.regs.rsp = s.regs.rsp - 40 := sp2.trans rsp1
  have pc2' : t2.pc = Insert4.entry+0x1a := pc2
  rw [Placement.at_pc t2 _ pc2']
  -- the sequence increment
  have read2 : t2.data.dmem.loadInt (t2.data.regs.rbx.toBitVec+16) 8 = some (seq.toNat : Int) := by
    rw [rbx2]
    exact pre.seqBefore caller (by omega) (by omega)
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (increment_layout4.agreement decoder.insert4) t2.data _
      (increment_region t2.data _ seq read2))
  rintro t3 ⟨pc3,regs3,mem3⟩
  rw [rbx2] at mem3
  have e36 : t3.data.regs.rsp.toBitVec + 4 = s.regs.rsp.toBitVec - .ofNat 64 36 := by
    rw [regs3, rsp2, UInt64.toBitVec_sub]
    show s.regs.rsp.toBitVec - 40#64 + 4#64 = s.regs.rsp.toBitVec - 36#64
    bv_omega
  have e48 : t3.data.regs.rsp.toBitVec - 8 = s.regs.rsp.toBitVec - .ofNat 64 48 := by
    rw [regs3, rsp2, UInt64.toBitVec_sub]
    show s.regs.rsp.toBitVec - 40#64 - 8#64 = s.regs.rsp.toBitVec - 48#64
    bv_omega
  have input : t3.data.dmem.loadInt t3.data.regs.r13.toBitVec 4 = some (network.toNat : Int) := by
    rw [mem3, regs3, r13two, load_store_apart _ _ _ _ _ _ keySeq,
      pre.before (by omega) (by omega) _ 4 keyStack keyBuffer]
    exact word
  have mapped : (t3.data.dmem.loadInt (t3.data.regs.rsp.toBitVec+4) 4).isSome = true := by
    rw [mem3, e36]
    apply storeInt_defined
    rw [← frame2.loadInt _ 4 (fun i hi h => by
      rcases h with h | h
      · exact below_disjoint _ 36 4 48 8 (by decide) (by decide) (by decide) _ ⟨i,hi,rfl⟩ h
      · exact caller.coverageStack _ (writes_bytes h)
          (below_sub _ 36 4 200 208 (by omega) (by omega) _ ⟨i,hi,rfl⟩))]
    exact pushed_mapped s _ _ (caller.below.load 36 4 (by omega) (by omega))
  obtain ⟨old0,mapped⟩ := Option.isSome_iff_exists.mp mapped
  have callWord : ((t3.data.dmem.storeInt (t3.data.regs.rsp.toBitVec+4) 4
      (Allowedips.swap32 network).toInt).loadInt (t3.data.regs.rsp.toBitVec-8) 8).isSome = true := by
    rw [mem3, regs3]
    exact storeInt_defined _ _ _ _ _ _ (storeInt_defined _ _ _ _ _ _ ready2.mapped)
  obtain ⟨old1,callWord⟩ := Option.isSome_iff_exists.mp callWord
  have pc3' : t3.pc = Insert4.entry+.ofNat 31 := pc3
  rw [Placement.at_pc t3 _ pc3']
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (region_eventually (body4_layout.agreement decoder.insert4) t3.data _
      (body4 t3.data network old0 old1 input mapped callWord))
  rintro a ⟨regs4,mem4,pc4⟩
  rw [e36, e48, mem3] at mem4
  have frames : Frames c s seq 48 t2.data.dmem a.data.dmem := by
    refine ⟨frame2,ready2.state,?_⟩
    rw [mem4]
    intro x hx
    exact ((storeInt_frame _ _ 4 _) x (fun h => hx
        (below_sub _ 36 4 48 16 (by omega) (by omega) x h))).trans
      ((storeInt_frame _ _ 8 _) x (fun h => hx (below_sub _ 48 8 48 16 (by omega) (by omega) x h)))
  have stack : a.data.regs.rsp = s.regs.rsp - 48 := by
    rw [regs4, regs3]
    show t2.data.regs.rsp - 8 = s.regs.rsp - 48
    rw [rsp2]
    apply UInt64.toBitVec_inj.mp
    show s.regs.rsp.toBitVec - 40#64 - 8#64 = s.regs.rsp.toBitVec - 48#64
    bv_omega
  refine ⟨pc4,stack,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [regs4, regs3]; exact rbx2
  · rw [regs4]; rfl
  · rw [regs4, regs3]
    show t2.data.regs.rsp + 4 = s.regs.rsp - 36
    rw [rsp2]
    apply UInt64.toBitVec_inj.mp
    show s.regs.rsp.toBitVec - 40#64 + 4#64 = s.regs.rsp.toBitVec - 36#64
    bv_omega
  · exact cidr_reg s.regs t3.data.regs a.data.regs (by rw [regs3]; exact rbp2) (by rw [regs4])
  · rw [regs4, regs3]; exact r12two
  · rw [stack, mem4]
    exact load64_store _ _ _
  · exact (frames.saved caller (by omega) (by omega) 8 (by omega) (by omega)).trans (pushed_r13 s)
  · exact (frames.saved caller (by omega) (by omega) 16 (by omega) (by omega)).trans (pushed_r12 s)
  · exact (frames.saved caller (by omega) (by omega) 24 (by omega) (by omega)).trans (pushed_rbp s)
  · exact (frames.saved caller (by omega) (by omega) 32 (by omega) (by omega)).trans (pushed_rbx s)
  · show a.data.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 36) 4 = _
    rw [mem4, below_load_store _ _ 36 4 48 8 _ (by decide) (by decide) (by decide)]
    exact load32_store _ _ _
  · exact frames.seqAfter caller (by omega) (by omega)
  · exact frames.total (by omega) (by omega)
  · exact frames.coverageAfter caller (by omega) (by omega)

theorem range_low (base : BitVec 64) (a : BitVec 64) (h : InRange base 8 a) : InRange base 16 a := by
  obtain ⟨i,hi,eq⟩ := h
  exact ⟨i,by omega,eq⟩

theorem range_high (base : BitVec 64) (a : BitVec 64) (h : InRange (base+8) 8 a) : InRange base 16 a := by
  obtain ⟨i,hi,eq⟩ := h
  refine ⟨8+i,by omega,?_⟩
  rw [eq, BitVec.ofNat_add, BitVec.add_assoc]
  rfl

/-- The v6 wrapper, entry to `add`'s entry. -/
theorem enter6 (fetch : Int64 → Option Decoded)
    (decoder : AllowedipsMutationDecoderAgreement fetch) (tracePc : TracePcContract fetch)
    {c : Context} {s : MachineData} {seq : BitVec 64} (caller : Caller c s seq)
    (high low : BitVec 64)
    (wordHigh : s.dmem.loadInt s.regs.rsi.toBitVec 8 = some (high.toNat : Int))
    (wordLow : s.dmem.loadInt (s.regs.rsi.toBitVec+8) 8 = some (low.toNat : Int))
    (keyStack : ∀ a, InRange s.regs.rsi.toBitVec 16 a →
      ¬InRange (s.regs.rsp.toBitVec - .ofNat 64 200) 200 a)
    (keyBuffer : ∀ a, InRange s.regs.rsi.toBitVec 16 a → ¬c.writes a)
    (keySeq : ∀ a, InRange s.regs.rsi.toBitVec 16 a → ¬InRange (s.regs.rdi.toBitVec+16) 8 a) :
    Eventually (instructionStep fetch) (fun t => t.pc = Add.entry ∧
      AtAdd c s seq false ((Allowedips.swap64 high).toNat*2^64+(Allowedips.swap64 low).toNat) t.data)
      ⟨s,Insert6.entry⟩ := by
  have start : (⟨s,Insert6.entry⟩ : MachineState) = ⟨s,Insert6.entry+.ofNat 0⟩ := rfl
  rw [start]
  -- prologue
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (prologue6_layout.agreement decoder.insert6) s _
      (prologue6 s _ (caller.below.load 8 8 (by omega) (by omega))
        (caller.below.load 16 8 (by omega) (by omega)) (caller.below.load 24 8 (by omega) (by omega))
        (caller.below.load 32 8 (by omega) (by omega))))
  rintro t1 ⟨regs1,mem1,pc1⟩
  have rsp1 : t1.data.regs.rsp = s.regs.rsp - 48 := by rw [regs1]
  have word1 : t1.data.regs.rsp.toBitVec - 8 = s.regs.rsp.toBitVec - .ofNat 64 56 := by
    rw [rsp1, UInt64.toBitVec_sub]
    show s.regs.rsp.toBitVec - 48#64 - 8#64 = s.regs.rsp.toBitVec - 56#64
    bv_omega
  have ready1 : CallsReady c t1.data := caller.ready 56 (by omega) (by omega) t1.data word1
    (by rw [rsp1]; exact aligned_sub _ 48 (by omega) (by omega) caller.aligned caller.room) mem1
  have pc1' : t1.pc = Insert6.entry+0x15 := pc1
  rw [Placement.at_pc t1 _ pc1']
  -- coverage callback
  apply eventually_trans (instructionStep fetch) _ _ _
    (Services.call fetch (Insert6.entry+0x15) "L_ffffffff810f31f0" .pc tracePc
      (decoder.insert6 _ _ (by rfl)) c t1.data ready1)
  rintro t2 ⟨pc2,sp2,bx2,bp2,r12_2,r13_2,_,_,ready2,frame2⟩
  rw [word1, mem1] at frame2
  have pre : Frames c s seq 56 t2.data.dmem
      (t2.data.dmem.storeInt (s.regs.rdi.toBitVec+16) 8 (1+seq).toInt) :=
    ⟨frame2,ready2.state,fun _ _ => rfl⟩
  have rbx2 : t2.data.regs.rbx = s.regs.rdi := bx2.trans (by rw [regs1])
  have rbp2 : t2.data.regs.rbp = .ofBitVec ((s.regs.get (.low .rdx .W32)).setWidth 64) :=
    bp2.trans (by rw [regs1])
  have r12two : t2.data.regs.r12 = s.regs.rsi := r12_2.trans (by rw [regs1])
  have r13two : t2.data.regs.r13 = s.regs.rcx := r13_2.trans (by rw [regs1])
  have rsp2 : t2.data.regs.rsp = s.regs.rsp - 48 := sp2.trans rsp1
  have pc2' : t2.pc = Insert6.entry+.ofNat 26 := pc2
  rw [Placement.at_pc t2 _ pc2']
  -- three arguments
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (pre6_layout.agreement decoder.insert6) t2.data _ (pre6 t2.data _))
  rintro p ⟨regsP,memP,pcP⟩
  have rbxP : p.data.regs.rbx = s.regs.rdi := by rw [regsP]; exact rbx2
  have rspP : p.data.regs.rsp = s.regs.rsp - 48 := by rw [regsP]; exact rsp2
  have r12P : p.data.regs.r12 = s.regs.rsi := by rw [regsP]; exact r12two
  have pcP' : p.pc = Insert6.entry+0x25 := pcP
  rw [Placement.at_pc p _ pcP']
  -- the sequence increment
  have readP : p.data.dmem.loadInt (p.data.regs.rbx.toBitVec+16) 8 = some (seq.toNat : Int) := by
    rw [rbxP, memP]
    exact pre.seqBefore caller (by omega) (by omega)
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (increment_layout6.agreement decoder.insert6) p.data _
      (increment_region p.data _ seq readP))
  rintro t3 ⟨pc3,regs3,mem3⟩
  rw [rbxP, memP] at mem3
  have e48 : t3.data.regs.rsp.toBitVec = s.regs.rsp.toBitVec - .ofNat 64 48 := by
    rw [regs3, rspP, UInt64.toBitVec_sub]
    rfl
  have e40 : t3.data.regs.rsp.toBitVec + 8 = s.regs.rsp.toBitVec - .ofNat 64 40 := by
    rw [e48]
    show s.regs.rsp.toBitVec - 48#64 + 8#64 = s.regs.rsp.toBitVec - 40#64
    bv_omega
  have e56 : t3.data.regs.rsp.toBitVec - 8 = s.regs.rsp.toBitVec - .ofNat 64 56 := by
    rw [e48]
    show s.regs.rsp.toBitVec - 48#64 - 8#64 = s.regs.rsp.toBitVec - 56#64
    bv_omega
  have r12three : t3.data.regs.r12 = s.regs.rsi := by rw [regs3]; exact r12P
  have t2mapped (k : Nat) (hk : 40 ≤ k) (hk' : k ≤ 48) :
      (t2.data.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 k) 8).isSome = true := by
    rw [← frame2.loadInt _ 8 (fun i hi h => by
      rcases h with h | h
      · exact below_disjoint _ k 8 56 8 (by omega) (by omega) (by omega) _ ⟨i,hi,rfl⟩ h
      · exact caller.coverageStack _ (writes_bytes h)
          (below_sub _ k 8 200 208 (by omega) (by omega) _ ⟨i,hi,rfl⟩))]
    exact pushed_mapped s _ _ (caller.below.load k 8 (by omega) (by omega))
  have inputHigh : t3.data.dmem.loadInt t3.data.regs.r12.toBitVec 8 = some (high.toNat : Int) := by
    rw [mem3, r12three, load_store_apart _ _ _ _ _ _ (fun x h => keySeq x (range_low _ x h)),
      pre.before (by omega) (by omega) _ 8 (fun x h => keyStack x (range_low _ x h))
        (fun x h => keyBuffer x (range_low _ x h))]
    exact wordHigh
  have mappedHigh : (t3.data.dmem.loadInt t3.data.regs.rsp.toBitVec 8).isSome = true := by
    rw [mem3, e48]
    exact storeInt_defined _ _ _ _ _ _ (t2mapped 48 (by omega) (by omega))
  obtain ⟨old0,mappedHigh⟩ := Option.isSome_iff_exists.mp mappedHigh
  have inputLow : (high6 t3.data high).loadInt (t3.data.regs.r12.toBitVec+8) 8 =
      some (low.toNat : Int) := by
    unfold high6
    rw [e48, load_store_apart _ _ _ _ _ _ (fun x h hs => keyStack x (range_high _ x (r12three ▸ h))
        (below_sub _ 48 8 200 200 (by omega) (by omega) x hs)),
      mem3, r12three, load_store_apart _ _ _ _ _ _ (fun x h => keySeq x (range_high _ x h)),
      pre.before (by omega) (by omega) _ 8 (fun x h => keyStack x (range_high _ x h))
        (fun x h => keyBuffer x (range_high _ x h))]
    exact wordLow
  have mappedLow : ((high6 t3.data high).loadInt (t3.data.regs.rsp.toBitVec+8) 8).isSome = true := by
    unfold high6
    rw [mem3, e40]
    exact storeInt_defined _ _ _ _ _ _ (storeInt_defined _ _ _ _ _ _ (t2mapped 40 (by omega) (by omega)))
  obtain ⟨old1,mappedLow⟩ := Option.isSome_iff_exists.mp mappedLow
  have callWord : ((low6 t3.data high low).loadInt (t3.data.regs.rsp.toBitVec-8) 8).isSome = true := by
    unfold low6 high6
    rw [mem3, regs3, regsP]
    exact storeInt_defined _ _ _ _ _ _ (storeInt_defined _ _ _ _ _ _
      (storeInt_defined _ _ _ _ _ _ ready2.mapped))
  obtain ⟨old2,callWord⟩ := Option.isSome_iff_exists.mp callWord
  have pc3' : t3.pc = Insert6.entry+.ofNat 42 := pc3
  rw [Placement.at_pc t3 _ pc3']
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (region_eventually (body6_layout.agreement decoder.insert6) t3.data _
      (body6 t3.data high low old0 old1 old2 inputHigh mappedHigh inputLow mappedLow callWord))
  rintro a ⟨regs4,mem4,pc4⟩
  unfold low6 high6 at mem4
  rw [e40, e56, e48, mem3] at mem4
  have frames : Frames c s seq 56 t2.data.dmem a.data.dmem := by
    refine ⟨frame2,ready2.state,?_⟩
    rw [mem4]
    intro x hx
    exact (((storeInt_frame _ _ 8 _) x (fun h => hx
        (below_sub _ 48 8 56 24 (by omega) (by omega) x h))).trans
      ((storeInt_frame _ _ 8 _) x (fun h => hx (below_sub _ 40 8 56 24 (by omega) (by omega) x h)))).trans
      ((storeInt_frame _ _ 8 _) x (fun h => hx (below_sub _ 56 8 56 24 (by omega) (by omega) x h)))
  have stack : a.data.regs.rsp = s.regs.rsp - 56 := by
    rw [regs4, regs3]
    show p.data.regs.rsp - 8 = s.regs.rsp - 56
    rw [rspP]
    apply UInt64.toBitVec_inj.mp
    show s.regs.rsp.toBitVec - 48#64 - 8#64 = s.regs.rsp.toBitVec - 56#64
    bv_omega
  have highBound := (Allowedips.swap64 high).isLt
  have lowBound := (Allowedips.swap64 low).isLt
  refine ⟨pc4,stack,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [regs4, regs3, regsP]
    show t2.data.regs.rbx + 8 = s.regs.rdi + 8
    rw [rbx2]
  · rw [regs4]; rfl
  · rw [regs4, regs3]; exact rspP
  · exact cidr_reg s.regs t2.data.regs a.data.regs rbp2 (by rw [regs4, regs3, regsP])
  · rw [regs4, regs3, regsP]; exact r13two
  · rw [stack, mem4]
    exact load64_store _ _ _
  · exact (frames.saved caller (by omega) (by omega) 8 (by omega) (by omega)).trans (pushed_r13 s)
  · exact (frames.saved caller (by omega) (by omega) 16 (by omega) (by omega)).trans (pushed_r12 s)
  · exact (frames.saved caller (by omega) (by omega) 24 (by omega) (by omega)).trans (pushed_rbp s)
  · exact (frames.saved caller (by omega) (by omega) 32 (by omega) (by omega)).trans (pushed_rbx s)
  · show a.data.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 48) 8 = _ ∧
      a.data.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 40) 8 = _
    constructor
    · rw [mem4, below_load_store _ _ 48 8 56 8 _ (by decide) (by decide) (by decide),
        below_load_store _ _ 48 8 40 8 _ (by decide) (by decide) (by decide), load64_store]
      congr 2
      omega
    · rw [mem4, below_load_store _ _ 40 8 56 8 _ (by decide) (by decide) (by decide), load64_store]
      congr 2
      omega
  · exact frames.seqAfter caller (by omega) (by omega)
  · exact frames.total (by omega) (by omega)
  · exact frames.coverageAfter caller (by omega) (by omega)

#print axioms enter4
#print axioms enter6

end C1Trunk
