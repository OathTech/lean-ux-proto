import C1BelowPrefixCommon

/-! Result C1, work package 3, prefix: from the cut (`add+0x156`) to the
selected node below the placement (`add+0x241`) when nothing was placed
(`rbx = 0`): the node below is the family's root, loaded through the saved
root-slot pointer at `rsp+8` (`add+0x601`). -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1 Binary.AllowedipsMutationImage
open Binary.Pair.Allowedips.Root Binary.Pair.Allowedips.ChildFinish
local instance : Labels := Image.linkedLabels

theorem selected_root (fetch : Int64 → Option Decoded)
    (decoder : AllowedipsMutationDecoderAgreement fetch) (tracePc : TracePcContract fetch)
    {names : Allowedips.Names} {world : World} {e : MachineState}
    {key cidr pid base downId slot : Nat} {d : Device} (c : Context)
    (checked : NodeInit.boundary names nodeOffsets world e key cidr pid=.ok base)
    (device : world.wg.dev=some d)
    (res : Res names c e.data base)
    (ready : CallsReady c e.data)
    (noParent : e.data.regs.rbx=0)
    (slotWord : e.data.dmem.loadInt (e.data.regs.rsp.toBitVec+8) 8=some ((names.table+slot : Nat) : Int))
    (slotBound : names.table+slot<2^64)
    (rooted : ∃ raw path, word e.data.dmem path (names.table+slot) 8=.ok raw ∧
      Trie.pointer names.trie.nodes path raw=.ok (some downId))
    (within : slot+8≤24) :
    ∃ m, NodeInit.effect e.data=.ok (m,base) ∧
      Eventually (instructionStep fetch) (Selected names c e.data d key cidr pid base downId m) e := by
  have fields := NodeInit.boundary_fields checked
  obtain ⟨actual,deviceAt,related,heapOk⟩ := assertAt_ok fields.asserted
  have equal : actual=d := Option.some.inj (deviceAt.symm.trans device)
  subst actual
  obtain ⟨memory,summary,execution⟩ := NodeInit.initialization_executes fetch decoder checked
  refine ⟨memory,summary,?_⟩
  have pending := NodeInit.pending_of_effect fields related heapOk summary
  have frame := (NodeInit.core_of_effect fields summary).2
  obtain ⟨raw,path,rootRead,rootPointer⟩ := rooted
  obtain ⟨nonzero,childNamed⟩ := Select.pointer_some_named rootPointer
  have rawBound : raw<2^64 := by
    have range := ((Trie.reconstruct_fields related.trie).nodeRange _ _ childNamed).2
    omega
  apply eventually_trans (instructionStep fetch) _ _ _ execution
  rintro a ⟨pcA,memA,registers,mappedA⟩
  have registerFacts : a.data.regs.rsp=e.data.regs.rsp ∧
      a.data.regs.rbx=e.data.regs.rbx ∧ a.data.regs.r12=e.data.regs.r12 ∧
      a.data.regs.r13=e.data.regs.r13 ∧ a.data.regs.r15=e.data.regs.r15 ∧
      a.data.regs.rbp=UInt64.ofNat (e.data.regs.rbp.toNat/8) ∧
      a.data.regs.r8=UInt64.ofNat base ∧ a.data.regs.r14=UInt64.ofNat (base+32) := by
    simpa only [NodeInit.registers,Bool.and_eq_true,beq_iff_eq,and_assoc] using registers
  obtain ⟨stack,bx,r12A,queryReg,r15A,bpA,allocation,r14A⟩ := registerFacts
  have fresh := (allocated_facts fields.allocated).2.2.1
  change base+72<2^64 at fresh
  have allocationNat : a.data.regs.r8.toNat=base := by
    rw [allocation]
    exact UInt64.toNat_ofNat_of_lt' (by change base<2^64; omega)
  have frameA : EqualOutside (NodeInit.EntryWrites names e.data base) e.data.dmem a.data.dmem := memA ▸ frame
  have pendingA : NodeInit.Pending names e.data d key cidr pid base a.data.dmem := memA ▸ pending
  have readyA := ready.frame stack frameA mappedA res.contextInit
  have queryA : AllowedipsChild.QueryWords a.data.dmem e.data.regs.r13.toBitVec e.data.regs.rbp.toNat key :=
    AllowedipsLoop.query_frame fields.family (Placement.queryLocals_fields fields.query)
      frameA fields.query_separated
  have slotA : a.data.dmem.loadInt (e.data.regs.rsp.toBitVec+8) 8=some ((names.table+slot : Nat) : Int) := by
    have kept := res.init_local frameA 8 8 (by decide) (by decide)
    exact kept.trans slotWord
  -- the save of the fresh node, the branch to `add+0x601`, the coverage call
  have slotMapped : (a.data.dmem.loadInt (.ofNat 64 (a.data.regs.rsp.toNat+24)) 8).isSome=true := by
    rw [stack]
    exact mappedA _ _ (res.local_mapped_nat 24 8 (by decide))
  have stored := store_total (value:=a.data.regs.r8.toNat) slotMapped
  have zero : a.data.regs.rbx=0 := bx.trans noParent
  have entryChecked : ChildSetup.entryEffect a.data=
      .ok (a.data.dmem.storeInt (.ofNat 64 (a.data.regs.rsp.toNat+24)) 8 a.data.regs.r8.toNat,0x601) := by
    simp only [ChildSetup.entryEffect,stored,zero,beq_self_eq_true,ite_true]
    rfl
  rw [Placement.at_pc a _ pcA]
  apply eventually_trans (instructionStep fetch) _ _ _
    (eventually_flight (ChildSetup.entry_checked fetch decoder entryChecked))
  rintro b ⟨⟨pcB,regsB,memB,frameB,_⟩,mappedB,_⟩
  have readyB : CallsReady c b.data := readyA.frame (by rw [regsB]) frameB mappedB (by
    intro x read written
    rw [stack] at written
    exact res.context x read (zone_locals (by decide) written))
  have here := decoder.add _ _ (show Add.fetch (Add.entry+0x601)=some _ from rfl)
  rw [Placement.at_pc b _ pcB]
  apply eventually_trans (instructionStep fetch) _ _ _
    (eventually_flight (Services.call fetch (Add.entry+0x601) "L_ffffffff810f31f0" .pc tracePc here c b.data readyB))
  rintro s2 ⟨⟨pcS,stackS,bxS,bpS,r12S,r13S,r14S,r15S,readyS,frameS⟩,mappedS,_⟩
  rw [regsB] at stackS bxS bpS r12S r13S r14S r15S frameS
  rw [stack] at frameS
  have memB' : b.data.dmem=a.data.dmem.storeInt (e.data.regs.rsp.toBitVec+24) 8 (base : Int) := by
    rw [memB,allocationNat,stack,slot_address]
    rfl
  have slotFrame : EqualOutside (InRange (e.data.regs.rsp.toBitVec+24) 8) a.data.dmem b.data.dmem :=
    memB' ▸ storeInt_frame _ _ _ _
  have frameAS : EqualOutside (Late e.data.regs.rsp c) a.data.dmem s2.data.dmem := by
    intro x outside
    exact (slotFrame x (fun h => outside (.inr (.inl h)))).trans (frameS x (fun h => outside (call_late h)))
  have pendingS := pendingA.frame frameAS
    (fun span member x inside late => res.projection span member x inside (late_after late))
    (fun x inside late => res.table x inside (late_after late))
  -- the three loads of `add+0x606`
  have slotS : s2.data.dmem.loadInt (s2.data.regs.rsp.toBitVec+0x8) 8=
      some ((BitVec.ofNat 64 (names.table+slot)).toNat : Int) := by
    rw [stackS,stack,BitVec.toNat_ofNat,Nat.mod_eq_of_lt slotBound]
    rw [←frameS.loadInt (e.data.regs.rsp.toBitVec+8) 8 (fun i bound written =>
      call_slot res (offset:=8) (by decide) ⟨i,bound,rfl⟩ written)]
    rw [←slotFrame.loadInt (e.data.regs.rsp.toBitVec+8) 8 (by
      rintro i bound ⟨j,boundJ,location⟩
      bv_omega)]
    exact slotA
  have baseS : s2.data.dmem.loadInt (s2.data.regs.rsp.toBitVec+0x18) 8=
      some ((BitVec.ofNat 64 base).toNat : Int) := by
    rw [stackS,stack,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : base<2^64)]
    rw [←frameS.loadInt (e.data.regs.rsp.toBitVec+24) 8 (fun i bound written =>
      call_slot res (offset:=24) (by decide) ⟨i,bound,rfl⟩ written)]
    rw [memB']
    exact load_store_word _ _ base (by omega)
  have rootS : s2.data.dmem.loadInt (BitVec.ofNat 64 (names.table+slot)) 8=
      some ((BitVec.ofNat 64 raw).toNat : Int) := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt rawBound]
    apply word_loadInt _ path
    rw [pendingS.table slot 8 within path]
    exact rootRead
  have topMapped : (s2.data.dmem.loadInt s2.data.regs.rsp.toBitVec 8).isSome=true := by
    rw [stackS,stack]
    have top : (e.data.dmem.loadInt e.data.regs.rsp.toBitVec 8).isSome=true := by
      simpa using res.local_mapped 0 8 (by decide)
    exact mappedS _ _ (mappedB _ _ (mappedA _ _ top))
  obtain ⟨old,oldRead⟩ := Option.isSome_iff_exists.mp topMapped
  have pcS' : s2.pc=Add.entry+0x606 := pcS
  rw [Placement.at_pc s2 _ pcS']
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (eventually_flight (region_eventually (Add_r606_layout.agreement decoder.add) s2.data _
      (root606 s2.data _ _ _ old slotS baseS rootS oldRead)))
  rintro t ⟨⟨pcT,regsT,memT⟩,mappedT,_⟩
  have memT' : t.data.dmem=s2.data.dmem.storeInt e.data.regs.rsp.toBitVec 8 (raw : Int) := by
    rw [memT,←store_unsigned _ _ 8 (BitVec.ofNat 64 raw),BitVec.toNat_ofNat,Nat.mod_eq_of_lt rawBound,
      stackS,stack]
  have topFrame : EqualOutside (InRange e.data.regs.rsp.toBitVec 8) s2.data.dmem t.data.dmem :=
    memT' ▸ storeInt_frame _ _ _ _
  have lateT : EqualOutside (Late e.data.regs.rsp c) a.data.dmem t.data.dmem := by
    intro x outside
    exact (frameAS x outside).trans (topFrame x (fun h => outside (late_top h)))
  exact {
    pc := pcT
    stack := by rw [regsT]; exact stackS.trans stack
    bx := by rw [regsT]; exact bxS.trans bx
    r12 := by rw [regsT]; exact r12S.trans r12A
    r13 := by rw [regsT]; exact r13S.trans queryReg
    r15 := by rw [regsT]; exact r15S.trans r15A
    bp := by rw [regsT]; exact bpS.trans bpA
    r14 := by rw [regsT]; exact r14S.trans r14A
    r8 := by rw [regsT]; rfl
    ready := readyS.frame (by rw [regsT]) topFrame mappedT (by
      intro x read top
      exact res.context x read (zone_locals (by decide) top))
    late := memA ▸ lateT
    mapped := fun address size h => mappedT _ _ (mappedS _ _ (mappedB _ _ (mappedA _ _ h)))
    pending := pendingA.frame lateT
      (fun span member x inside late => res.projection span member x inside (late_after late))
      (fun x inside late => res.table x inside (late_after late))
    query := AllowedipsLoop.query_frame fields.family queryA lateT
      (fun x inside late => res.query x inside (late_after late))
    down := ⟨raw,nonzero,childNamed,by rw [memT']; exact load_store_word _ _ raw rawBound⟩ }

#print axioms selected_root
end Binary.Statements.C1.Proof
