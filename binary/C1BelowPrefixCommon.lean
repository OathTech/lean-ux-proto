import C1BelowPrefixHeld
import AllowedipsPlacementCommon

/-! Result C1, work package 3, prefix: from the selected node below the
placement (`add+0x241`) through the save, the coverage call, `common_bits`
and the comparison callback to `add+0x267`. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1 Binary.AllowedipsMutationImage
open Binary.Pair.Allowedips.Root Binary.Pair.Allowedips.ChildFinish Binary.AllowedipsRelation
local instance : Labels := Image.linkedLabels

/-- `Placement.Frame.common` (landed) with `r14` exported as well. -/
theorem frame_common (fetch : Int64 → Option Decoded)
    (decoder : AllowedipsDecoderAgreement fetch) (callbacks : CommonBits.Callbacks fetch)
    (pc : Int64) (here : fetch pc=some ⟨Instrumentation.callInstruction "L_ffffffff813a0950",5⟩)
    (i : CommonBits.Input) {base c s} (frame : Placement.Frame base c s)
    (caller : CommonBits.CallerAt i c s (pc+5)) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=pc+5 ∧ Placement.Frame base c t.data ∧ t.data.regs.rbx=s.regs.rbx ∧
      t.data.regs.rbp=s.regs.rbp ∧ t.data.regs.r14=s.regs.r14 ∧
      (t.data.regs.get (.low .rax .W8)).toNat=i.result ∧
      t.data.dmem.loadInt base.regs.rsp.toBitVec 8=s.dmem.loadInt base.regs.rsp.toBitVec 8) ⟨s,pc⟩ := by
  have executed := CommonBits.Sequential.call_run fetch decoder callbacks pc here i c s caller
  apply eventually_weaken (instructionStep fetch) _ _ _ _ executed
  rintro t ⟨pc,sp,bx,bp,r12,r13,r14,r15,answer,covered,written,mapped⟩
  refine ⟨pc,?_,bx,bp,r14,answer,frame.parent_preserved written⟩
  apply frame.after sp r13 r12 r15 covered
  · simpa only [frame.stack] using mapped
  · intro a outside
    apply written a
    rintro (scratch | buffer)
    · exact outside (.inl (Placement.scratch_subset (by simpa only [CommonBits.CallerScratch,frame.stack] using scratch)))
    · exact outside (.inr buffer)

theorem load_store_word (m : DataMem) (address : BitVec 64) (value : Nat) (bound : value<2^64) :
    (m.storeInt address 8 (value : Int)).loadInt address 8=some (value : Int) := by
  have read := MemoryBytes.loadInt_store_subword m address 8 (value : Int) (by decide) 0 8 (by decide)
  have reduce : (value : Int)%18446744073709551616=(value : Int) :=
    Int.emod_eq_of_lt (by omega) (by have h : value<18446744073709551616 := bound; omega)
  simpa [reduce] using read

theorem family_byte (regs : Reg64s) (x y : UInt64) (bits : Nat) (family : bits=32 ∨ bits=128)
    (width : regs.r15=.ofNat bits) :
    Reg64s.get {regs with
        rdi := x
        rsi := y
        rdx := .ofBitVec ((regs.get (.low .r15 .W32)).setWidth 64)} (.low .rdx .W8)=
      .ofNat 8 bits := by
  rcases family with rfl | rfl <;>
    simp [width,Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop]

theorem low8_r13 (regs source : Reg64s)
    (moved : regs.r13=.ofBitVec ((source.get (.low .rax .W32)).setWidth 64)) :
    regs.get (.low .r13 .W8)=source.get (.low .rax .W8) := by
  simp [moved,Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop]
  ext i bound
  simp [show i<64 from by omega,show i<32 from by omega]

/-- The key bytes of a named node are read by reconstruction, hence outside
the zone and the coverage buffer. -/
theorem Res.key_apart {names : Allowedips.Names} {c : Context} {e : MachineData} {base : Nat}
    (res : Res names c e base) {id address : Nat} (named : (id,address) ∈ names.trie.nodes)
    {a : BitVec 64} (inside : InRange (BitVec.ofNat 64 address+32) 16 a) :
    ¬(Zone e.regs.rsp a ∨ c.writes a) := by
  obtain ⟨i,bound,location⟩ := inside
  have member (offset : Nat) (field : (offset,8) ∈ nodeFields nodeOffsets) :
      (address+offset,8) ∈ readSpans (names.allocated base) nodeOffsets :=
    List.mem_append_right _ (List.mem_append_left _ (List.mem_flatMap.mpr
      ⟨(id,address),List.mem_append_left _ named,List.mem_map.mpr ⟨(offset,8),field,rfl⟩⟩))
  by_cases first : i<8
  · refine res.projection _ (member 32 (by decide)) a ⟨i,first,?_⟩
    rw [location]
    bv_omega
  · refine res.projection _ (member 40 (by decide)) a ⟨i-8,by omega,?_⟩
    rw [location]
    bv_omega

/-- The state at `add+0x267`: `Held`, and the low byte of `r13` is
`common_bits(down, key, bits)`. -/
structure Compared (names : Allowedips.Names) (c : Context) (e : MachineData) (d : Device)
    (key cidr pid base child bits stored : Nat) (m : DataMem) (t : MachineState) : Prop where
  pc : t.pc=Add.entry+0x267
  held : Held names c e d key cidr pid base child m t.data
  common : (t.data.regs.get (.low .r13 .W8)).toNat=AllowedipsRelation.common bits stored key

theorem writes_late {stack other : UInt64} {c : Context} {a : BitVec 64} (same : other=stack)
    (written : Placement.Writes other c a) : Late stack c a := by
  subst same
  exact written.elim .inl (fun buffer => .inr (.inr buffer))

/-- From the selected node below the placement to the comparison. -/
theorem compared (fetch : Int64 → Option Decoded)
    (mutation : AllowedipsMutationDecoderAgreement fetch) (lookup : AllowedipsDecoderAgreement fetch)
    (callbacks : CommonBits.Callbacks fetch) (tracePc : TracePcContract fetch)
    (cmp : AllowedipsTraceCmp1Contract fetch)
    {names : Allowedips.Names} {world : World} {e t : MachineState}
    {key cidr pid base downId : Nat} {d : Device} {downNode : AipNode} {m : DataMem} (c : Context)
    (fields : NodeInit.BoundaryFields names nodeOffsets world e key cidr pid base)
    (related : Corresponds names nodeOffsets e.data.dmem d)
    (res : Res names c e.data base)
    (hasDown : d.nodes.get? downId=some downNode)
    (downWidth : downNode.bitlen=e.data.regs.rbp.toNat)
    (keyBound : key<2^e.data.regs.rbp.toNat)
    (sel : Selected names c e.data d key cidr pid base downId m t) :
    ∃ child, child≠0 ∧ (downId,child) ∈ names.trie.nodes ∧
      Eventually (instructionStep fetch)
        (Compared names c e.data d key cidr pid base child e.data.regs.rbp.toNat downNode.bits m) t := by
  obtain ⟨child,nonzero,childNamed,childRead⟩ := sel.down
  refine ⟨child,nonzero,childNamed,?_⟩
  have family := fields.family
  have childBound : child<2^64 := by
    have range := ((Trie.reconstruct_fields related.trie).nodeRange _ _ childNamed).2
    omega
  have fresh := (allocated_facts fields.allocated).2.2.1
  change base+72<2^64 at fresh
  -- the save of the fresh node at `rsp+24`
  obtain ⟨old,oldRead⟩ := Option.isSome_iff_exists.mp (sel.mapped _ _ (res.local_mapped 24 8 (by decide)))
  have layout1 : LaidOut Add.fetch (Add.entry+0x241) (Add.r241.take 1) := by binary_layout
  rw [Placement.at_pc t _ sel.pc]
  apply eventually_trans (instructionStep fetch) _ _ _
    (eventually_flight (region_eventually (layout1.agreement mutation.add) t.data _
      (save241 t.data old (by rw [sel.stack]; exact oldRead))))
  rintro u ⟨⟨pcU,regsU,memU⟩,mappedU,_⟩
  have r8Nat : t.data.regs.r8.toBitVec.toNat=base := by
    rw [sel.r8]
    exact UInt64.toNat_ofNat_of_lt' (by change base<2^64; omega)
  have memU' : u.data.dmem=t.data.dmem.storeInt (e.data.regs.rsp.toBitVec+24) 8 (base : Int) := by
    rw [memU,←store_unsigned _ _ 8 t.data.regs.r8.toBitVec,r8Nat,sel.stack]
  have slotFrame : EqualOutside (InRange (e.data.regs.rsp.toBitVec+24) 8) t.data.dmem u.data.dmem :=
    memU' ▸ storeInt_frame _ _ _ _
  have slotZone : ∀ x, InRange (e.data.regs.rsp.toBitVec+24) 8 x → Zone e.data.regs.rsp x :=
    fun x inside => zone_local (offset:=24) (by decide) inside
  have stackU : u.data.regs.rsp=e.data.regs.rsp := by rw [regsU]; exact sel.stack
  have readyU : CallsReady c u.data := sel.ready.frame (by rw [regsU]) slotFrame mappedU
    (fun x read inside => res.context x read (slotZone x inside))
  have heldU : Held names c e.data d key cidr pid base child m u.data := {
    stack := stackU
    bx := by rw [regsU]; exact sel.bx
    r12 := by rw [regsU]; exact sel.r12
    r15 := by rw [regsU]; exact sel.r15
    bp := by rw [regsU]; exact sel.bp
    r14 := by rw [regsU]; exact sel.r14
    ready := readyU
    late := fun a outside => (sel.late a outside).trans (slotFrame a (fun h => outside (.inr (.inl h))))
    mapped := fun address size h => mappedU _ _ (sel.mapped _ _ h)
    pending := sel.pending.frame slotFrame
      (fun span member x within slot => res.projection span member x within (.inl (slotZone x slot)))
      (fun x within slot => res.table x within (.inl (slotZone x slot)))
    query := AllowedipsLoop.query_frame family sel.query slotFrame
      (fun x within slot => res.query x within (.inl (slotZone x slot)))
    down := by
      rw [←slotFrame.loadInt e.data.regs.rsp.toBitVec 8 (by
        rintro i bound ⟨j,boundJ,location⟩
        bv_omega)]
      exact childRead
    saved := by rw [memU']; exact load_store_word _ _ base (by omega) }
  have r13U : u.data.regs.r13=e.data.regs.r13 := by rw [regsU]; exact sel.r13
  -- the coverage call at `add+0x246`
  have here := mutation.add _ _ (show Add.fetch (Add.entry+0x246)=some _ from rfl)
  rw [Placement.at_pc u _ pcU]
  apply eventually_trans (instructionStep fetch) _ _ _
    (eventually_flight (Services.call fetch (Add.entry+0x246) "L_ffffffff810f31f0" .pc tracePc here c u.data readyU))
  rintro v ⟨⟨pcV,stackV,bxV,bpV,r12V,r13V,r14V,r15V,readyV,frameV⟩,mappedV,_⟩
  rw [stackU] at frameV
  have heldV := heldU.step res family _ stackV bxV r12V r15V bpV r14V readyV mappedV frameV
    (fun a written => call_late written)
    (fun a slot => call_slot res (offset:=24) (by decide) slot)
    (by
      symm
      apply frameV.loadInt
      intro i bound written
      exact call_slot res (offset:=0) (by decide) ⟨i,bound,by simp⟩ written)
  -- the arguments of `common_bits`
  have pcV' : v.pc=Add.entry+0x24b := pcV
  have layout3 : LaidOut Add.fetch (Add.entry+0x24b) (Add.r24b.take 3) := by binary_layout
  have downV : v.data.dmem.loadInt v.data.regs.rsp.toBitVec 8=
      some ((BitVec.ofNat 64 child).toNat : Int) := by
    rw [heldV.stack,BitVec.toNat_ofNat,Nat.mod_eq_of_lt childBound]
    exact heldV.down
  rw [Placement.at_pc v _ pcV']
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (layout3.agreement mutation.add) v.data _ (args24b v.data (.ofNat 64 child) downV))
  rintro w ⟨pcW,regsW,memW⟩
  have heldW : Held names c e.data d key cidr pid base child m w.data :=
    heldV.step res family (fun _ => False) (by simp [regsW]) (by simp [regsW]) (by simp [regsW])
      (by simp [regsW]) (by simp [regsW]) (by simp [regsW])
      (readyV.congr memW (by simp [regsW])) (memW ▸ MappedLe.refl _) (memW ▸ fun _ _ => rfl)
      (fun _ h => h.elim) (fun _ _ h => h) (by rw [memW])
  have frameW : Placement.Frame w.data c w.data := ⟨heldW.ready,rfl,rfl,rfl,rfl,
    fun n bound => by rw [heldW.stack]; exact heldW.mapped _ _ (res.below_mapped n bound),
    fun a read inside => res.context a read
      (zone_scratch (n:=56) (by decide) (by rw [heldW.stack] at inside; exact inside)),
    fun _ _ => rfl⟩
  have decoded := heldW.pending.old_node related childNamed hasDown
  have keyFields0 := Trie.decoded_key (query:=key) (Trie.decodeNode_fields decoded)
    (by change key<2^downNode.bitlen; rw [downWidth]; exact keyBound)
  change KeyFields w.data.dmem (.ofNat 64 (child+32)) downNode.bitlen downNode.bits key at keyFields0
  have rdiW : w.data.regs.rdi.toBitVec=BitVec.ofNat 64 child := by rw [regsW]
  have rsiW : w.data.regs.rsi=e.data.regs.r13 := by rw [regsW]; exact r13V.trans r13U
  have keyFields : KeyFields w.data.dmem (w.data.regs.rdi.toBitVec+32) e.data.regs.rbp.toNat downNode.bits key := by
    rw [rdiW,←downWidth]
    rw [BitVec.ofNat_add] at keyFields0
    exact keyFields0
  have width : v.data.regs.r15=.ofNat e.data.regs.rbp.toNat := by
    rw [heldV.r15,←fields.bits]
    simp
  have byte : w.data.regs.get (.low .rdx .W8)=.ofNat 8 e.data.regs.rbp.toNat := by
    rw [regsW]
    exact family_byte v.data.regs _ _ _ family width
  have caller := frameW.input_caller e.data.regs.rbp.toNat downNode.bits key (Add.entry+0x25a) family byte
    keyFields (by rw [rsiW]; exact heldW.query)
    (by
      intro a read written
      have inside : InRange (BitVec.ofNat 64 child+32) 16 a := by
        rw [rdiW] at read
        unfold KeyReads at read
        split at read
        · obtain ⟨i,bound,location⟩ := read
          exact ⟨i,by omega,location⟩
        · rcases read with ⟨i,bound,location⟩|⟨_,i,bound,location⟩
          · exact ⟨i,by omega,location⟩
          · refine ⟨8+i,by omega,?_⟩
            rw [location]
            bv_omega
      exact res.key_apart childNamed inside (late_after (writes_late heldW.stack written)))
    (by
      intro a read written
      rw [rsiW] at read
      exact res.query a read (late_after (writes_late heldW.stack written)))
  have called := frame_common fetch lookup callbacks (Add.entry+0x255) (mutation.add _ _ (by rfl))
    (Common.callInput w.data e.data.regs.rbp.toNat downNode.bits key (Add.entry+0x25a)) frameW caller
  rw [Placement.at_pc w _ pcW]
  apply eventually_trans (instructionStep fetch) _ _ _ (eventually_flight called)
  rintro x ⟨⟨pcX,frameX,bxX,bpX,r14X,answer,parent⟩,mappedX,_⟩
  rw [common_input_result _ _ _ _ _ family keyFields.1 keyFields.2.1] at answer
  have heldX := heldW.step res family (Placement.Writes w.data.regs.rsp c) frameX.stack bxX frameX.cidr
    frameX.bits bpX r14X frameX.ready mappedX frameX.memory
    (fun a written => writes_late heldW.stack written)
    (by
      rintro a ⟨i,bound,location⟩ (⟨j,boundJ,locationJ⟩|buffer)
      · rw [heldW.stack,location] at locationJ
        bv_omega
      · exact res.context a (writes_bytes buffer) (slotZone a ⟨i,bound,location⟩))
    (by rw [←heldW.stack]; exact parent)
  -- the comparison callback
  obtain ⟨oldWord,wordRead⟩ := Option.isSome_iff_exists.mp frameX.ready.mapped
  have pcX' : x.pc=Add.entry+0x25a := pcX
  have region := region_eventually (Add_r25a_layout.agreement mutation.add) x.data _ (cmp25a x.data oldWord wordRead)
  have called5 := CommonBitsCoverage.region_callback fetch (.ofNat 0xffffffff810f4040) (Add.entry+0x267) .cmp1 cmp c
    ⟨x.data,Add.entry+0x25a⟩ x.data
    {x.data.regs with
      rdi := .ofBitVec ((x.data.regs.get (.low .r12 .W32)).setWidth 64),
      r13 := .ofBitVec ((x.data.regs.get (.low .rax .W32)).setWidth 64),
      rsi := .ofBitVec ((x.data.regs.get (.low .rax .W32)).setWidth 64)} frameX.ready region
  rw [Placement.at_pc x _ pcX']
  apply eventually_weaken (instructionStep fetch) _ _ _ _ (eventually_flight called5)
  rintro y ⟨⟨pcY,spY,bxY,bpY,r12Y,r13Y,r14Y,r15Y,readyY,writtenY⟩,mappedY,_⟩
  rw [heldX.stack] at writtenY
  refine ⟨pcY,heldX.step res family _ spY bxY r12Y r15Y bpY r14Y readyY mappedY writtenY
    (fun a written => call_late written)
    (fun a slot => call_slot res (offset:=24) (by decide) slot)
    (by
      symm
      apply writtenY.loadInt
      intro i bound written
      exact call_slot res (offset:=0) (by decide) ⟨i,bound,by simp⟩ written),?_⟩
  rw [low8_r13 y.data.regs x.data.regs r13Y]
  exact answer

#print axioms compared
end Binary.Statements.C1.Proof
