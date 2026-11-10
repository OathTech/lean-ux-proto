import C1TrunkTail
/-! Result C1, package 2 (origin: trial T4, `task/binary-trials:binary-trials/t4`, copied and trimmed): the failure exits of the empty-root path on the machine side
(-ENOMEM after a failed allocation, -EINVAL for a too-long prefix). -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips Binary.AllowedipsMutationImage
open Binary.TrustBase Binary.CommonBitsCoverage Binary.Instrumentation
open Leanux Leanux.WG
local instance : Labels := Image.linkedLabels

/-- +0x692: the -ENOMEM result and the jump to the common exit. -/
theorem nomem_code (s : MachineData) :
    (Placement.physical Add.r692 0x692 s).All (fun t =>
      t.data.regs={s.regs with rbx := 0xfffffff4} ∧ t.data.dmem=s.dmem ∧ t.pc=Add.entry+0x549) := by
  simp [Placement.physical,Add.r692,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    Operand.interp,MachineData.set,MachineData.setReg,ConstExpr.interp,RelRegOrMem.interp,
    Reg64s.set,Reg64s.set64,Effects.All,Add.entry]
  decide

/-- +0x544: the -EINVAL result, falling through to the common exit. -/
theorem inval_code (s : MachineData) :
    (Placement.physical Add.r544 0x544 s).All (fun t =>
      t.data.regs={s.regs with rbx := 0xffffffea} ∧ t.data.dmem=s.dmem ∧ t.pc=Add.entry+0x549) := by
  simp [Placement.physical,Add.r544,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    Operand.interp,MachineData.set,MachineData.setReg,ConstExpr.interp,
    Reg64s.set,Reg64s.set64,Effects.All,Add.entry]

/-- The part of the entry assertion the failure exits need: no peer, key,
cache or allocator-layout facts. -/
structure EntryBase (names : Allowedips.Names) (c : Context) (aw : BitVec 64 → Prop) (world : World)
    (s0 : MachineData) (bits cidr : Nat) (ra : UInt64) (d : Device) : Prop where
  resources : Resources c s0
  returnWord : s0.dmem.loadInt s0.regs.rsp.toBitVec 8 = some (ra.toNat : Int)
  device : world.wg.dev = some d
  asserted : assertAt names Root.nodeOffsets s0.dmem world = .ok ()
  family : bits = 32 ∨ bits = 128
  argBits : (s0.regs.get (.low .rsi .W32)).toNat = bits
  argCidr : (s0.regs.get (.low .rcx .W32)).toNat = cidr
  readApart : ∀ span ∈ readSpans names Root.nodeOffsets, ∀ a, span.contains a →
    ¬Window s0 a ∧ ¬c.writes a ∧ ¬aw a
  awApart : ∀ a, aw a → ¬Window s0 a ∧ ¬c.bytes a

/-- A failure exit: from +0x549 with the error code in rbx, memory equal to a
live state's outside the callee return word and the allocator's footprint. -/
theorem failure_tail (fetch : Int64 → Option Decoded)
    (decoder : AllowedipsMutationDecoderAgreement fetch) (tracePc : TracePcContract fetch)
    {names : Allowedips.Names} {c : Context} {aw : BitVec 64 → Prop} {world : World}
    {s0 u w : MachineData} {bits cidr : Nat} {ra : UInt64} {d : Device}
    (entry : EntryBase names c aw world s0 bits cidr ra d)
    (live : Live c s0 u) (spW : w.regs.rsp = u.regs.rsp) (readyW : CallsReady c w)
    (frameU : EqualOutside (fun x => InRange (u.regs.rsp.toBitVec-8) 8 x ∨ aw x) u.dmem w.dmem) :
    Eventually (instructionStep fetch) (fun t =>
      Returned ⟨s0,Add.entry⟩ t ra ∧
      t.data.regs.rax = .ofBitVec ((w.regs.get (.low .rbx .W32)).setWidth 64) ∧
      c.At t.data.dmem ∧
      Corresponds names Root.nodeOffsets t.data.dmem d ∧
      heap names (target d) t.data.dmem = .ok () ∧
      EqualOutside (fun a => Window s0 a ∨ c.writes a ∨ aw a) s0.dmem t.data.dmem)
      ⟨w,Add.entry+0x549⟩ := by
  have word := call_word s0 u live.stack
  have total : EqualOutside (fun x => Window s0 x ∨ c.writes x ∨ aw x) s0.dmem w.dmem := by
    intro x outside
    refine ((memory_frame s0 8 (by decide)) x (fun h => outside (.inl ?_))).trans
      ((live.frame x (fun h => outside ?_)).trans (frameU x (fun h => outside ?_)))
    · rw [frame_base] at h
      exact window_sub s0 8 96 (by decide) x h
    · rcases h with p | cw
      · exact .inl (window_sub s0 0 8 (by decide) x (by simpa using p))
      · exact .inr (.inl cw)
    · rw [word] at h
      rcases h with p | x'
      · exact .inl (window_sub s0 0 8 (by decide) x (by simpa using p))
      · exact .inr (.inr x')
  have loadW : ∀ off n : Nat, 8 ≤ off → off+n ≤ 112 →
      w.dmem.loadInt (s0.regs.rsp.toBitVec-104+.ofNat 64 off) n =
        (memory s0 8).loadInt (s0.regs.rsp.toBitVec-104+.ofNat 64 off) n := by
    intro off n lo hi
    rw [← frameU.loadInt _ n (fun i ib written => by
      have inside : InRange (s0.regs.rsp.toBitVec-104+.ofNat 64 off) n
          (s0.regs.rsp.toBitVec-104+.ofNat 64 off+.ofNat 64 i) := ⟨i,ib,rfl⟩
      rcases written with p | x'
      · rw [word] at p
        exact InRange.offset_disjoint (s0.regs.rsp.toBitVec-104) off n 0 8 (by omega) (by omega)
          (.inr (by omega)) _ inside (by simpa using p)
      · exact (entry.awApart _ x').1 (window_sub s0 off n hi _ inside))]
    exact live.window_load entry.resources off n lo hi
  obtain ⟨d',device',related,shape⟩ := assertAt_ok entry.asserted
  cases Option.some.inj (entry.device.symm.trans device')
  have projApart : ∀ span ∈ readSpans names Root.nodeOffsets, ∀ x, span.contains x →
      ¬(Window s0 x ∨ c.writes x ∨ aw x) := by
    intro span member x inside h
    obtain ⟨nw,ncw,naw⟩ := entry.readApart span member x inside
    rcases h with w' | cw | x'
    · exact nw w'
    · exact ncw cw
    · exact naw x'
  have relatedW : Corresponds names Root.nodeOffsets w.dmem d :=
    (reconstruct_frame names Root.nodeOffsets total projApart).symm.trans related
  have shapeW := (heap_frame names Root.nodeOffsets (target d) total
    (fun span member => projApart span (metadata_read member))).symm.trans shape
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (finish_tail fetch decoder tracePc entry.resources entry.returnWord readyW
      (spW.trans live.stack) loadW relatedW shapeW
      (fun span member x inside => ⟨(entry.readApart span member x inside).1,
        (entry.readApart span member x inside).2.1⟩))
  rintro t ⟨pcT,rax,rsp,rbx,rbp,r12,r13,r14,r15,cov,relatedT,shapeT,frameT⟩
  refine ⟨⟨pcT,rsp,rbx,rbp,r12,r13,r14,r15⟩,rax,cov,relatedT,shapeT,?_⟩
  intro x outside
  exact (total x outside).trans (frameT x (fun h => outside (by
    rcases h with w' | cw
    · exact .inl w'
    · exact .inr (.inl cw))))

/-- The -EINVAL path for a too-long prefix on the machine side: no allocator
is involved. `byte` is the C type of `cidr` (u8): the image compares bytes. -/
theorem add_inval_machine (fetch : Int64 → Option Decoded)
    (decoder : AllowedipsMutationDecoderAgreement fetch)
    (tracePc : TracePcContract fetch) (cmp : AllowedipsTraceCmp1Contract fetch)
    {names : Allowedips.Names} {c : Context} {aw : BitVec 64 → Prop} {world : World}
    {s0 : MachineData} {bits cidr : Nat} {ra : UInt64} {d : Device}
    (entry : EntryBase names c aw world s0 bits cidr ra d)
    (long : cidr > bits) (byte : cidr < 256) :
    Eventually (instructionStep fetch) (fun t =>
      Returned ⟨s0,Add.entry⟩ t ra ∧ t.data.regs.rax = 0xffffffea ∧ c.At t.data.dmem ∧
      Corresponds names Root.nodeOffsets t.data.dmem d ∧
      heap names (target d) t.data.dmem = .ok () ∧
      EqualOutside (fun a => Window s0 a ∨ c.writes a ∨ aw a) s0.dmem t.data.dmem)
      ⟨s0,Add.entry⟩ := by
  have r := entry.resources
  have small : bits < 256 := by rcases entry.family with h | h <;> omega
  have start : (⟨s0,Add.entry⟩ : MachineState) = ⟨s0,Add.entry+.ofNat 0⟩ := rfl
  rw [start]
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (prologue_layout.agreement decoder.add) s0 _ (prologue s0 r.slots))
  rintro t1 ⟨regs1,mem1,pc1⟩
  have live1 := Live.initial r t1.data regs1 mem1
  rw [Placement.at_pc t1 _ pc1]
  apply eventually_trans (instructionStep fetch) _ _ _
    (live1.call fetch tracePc (Add.entry+0x25) (decoder.add _ _ (by rfl)))
  rintro t2 ⟨pc2,live2,_⟩
  have pc2' : t2.pc = Add.entry+0x2a := pc2
  rw [Placement.at_pc t2 _ pc2']
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
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (Add_r34_layout.agreement decoder.add) t3.data _ (cidr_guard t3.data))
  rintro t4 ⟨regs4,mem4,pc4⟩
  have live4 : Live c s0 t4.data := live3.quiet mem4 (by rw [regs4]) (by rw [regs4]) (by rw [regs4])
    (by rw [regs4]) (by rw [regs4]) (by rw [regs4])
  have bitsByte : (t3.data.regs.get (.low .rbp .W8)).toNat = bits :=
    low8_rbp _ bits entry.argBits small _ live3.bits
  have cidrByte : (t3.data.regs.get (.low .r15 .W8)).toNat = cidr :=
    low8_r15 _ cidr entry.argCidr byte _ live3.cidr15
  rw [bitsByte,cidrByte,ite_eq_left (by omega)] at pc4
  rw [Placement.at_pc t4 _ pc4]
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (Add_r544_layout.agreement decoder.add) t4.data _ (inval_code t4.data))
  rintro w ⟨regsW,memW,pcW⟩
  have spW : w.data.regs.rsp = t4.data.regs.rsp := by rw [regsW]
  have readyW : CallsReady c w.data := live4.ready.congr memW spW
  rw [Placement.at_pc w _ pcW]
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (failure_tail fetch decoder tracePc entry live4 spW readyW (by rw [memW]; exact fun _ _ => rfl))
  rintro t ⟨returned,rax,rest⟩
  refine ⟨returned,?_,rest⟩
  rw [rax,regsW]
  rfl

#print axioms failure_tail
#print axioms add_inval_machine
end C1Trunk
